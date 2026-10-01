-- Prove2me | solution 1 for BayesRouting.VOI.loadPotential_strictConvex
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T14:35:18.533806+00:00
-- url     : https://prove2.me/submissions/170d3b30-8a2e-4de2-af7f-7e4f0c82f4a0

import Definitions.Def_BayesRouting_VOI_Potential
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic

open BayesRouting.VOI
open scoped Topology ContDiff

namespace CBayes

theorem primitive_deriv {f : ℝ → ℝ} (hf : Continuous f) (x : ℝ) :
    HasDerivAt (fun y => ∫ z in (0 : ℝ)..y, f z) (f x) x :=
  intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable _ _)
    hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt

theorem primitive_C1 {f : ℝ → ℝ} (hf : Continuous f) :
    ContDiff ℝ 1 (fun y => ∫ z in (0 : ℝ)..y, f z) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun x => (primitive_deriv hf x).differentiableAt, ?_⟩
  have heq : deriv (fun y => ∫ z in (0 : ℝ)..y, f z) = f := funext fun x => (primitive_deriv hf x).deriv
  rw [heq]
  exact hf

theorem primitive_C2 {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) :
    ContDiff ℝ 2 (fun y => ∫ z in (0 : ℝ)..y, f z) := by
  rw [show (2 : ℕ∞ω) = 1 + 1 by rfl, contDiff_succ_iff_deriv]
  refine ⟨fun x => (primitive_deriv hf.continuous x).differentiableAt, by norm_num, ?_⟩
  have heq : deriv (fun y => ∫ z in (0 : ℝ)..y, f z) = f :=
    funext fun x => (primitive_deriv hf.continuous x).deriv
  rw [heq]
  exact hf

variable {I : Type} [Fintype I] [DecidableEq I] {T : I → Type} [∀ i, Fintype (T i)]
  [∀ i, DecidableEq (T i)] [∀ i, Nonempty (T i)] {S E R : Type} [Fintype S] [Fintype E]
  [DecidableEq E] [Fintype R] [DecidableEq R] [Nonempty R]

theorem typeProb_pos (G : Game I T S E R) (i : I) (ti : T i) : 0 < typeProb G i ti := by
  classical
  let t : (k : I) → T k := Function.update (fun k => Classical.choice (inferInstance : Nonempty (T k))) i ti
  have ht : t i = ti := by simp [t]
  have hle : (∑ s, G.prior s t) ≤ typeProb G i ti := by
    unfold typeProb
    rw [Finset.sum_comm]
    apply Finset.single_le_sum (f := fun t => ∑ s, G.prior s t)
      (fun t _ => Finset.sum_nonneg (fun s _ => G.prior_nonneg s t))
    simp [ht]
  exact (G.prior_full_support t).trans_le hle

theorem potential_C1 (G : Game I T S E R) : ContDiff ℝ 1 (potential G) := by
  unfold potential
  apply ContDiff.sum
  intro s hs
  apply ContDiff.sum
  intro e he
  apply ContDiff.sum
  intro t ht
  apply contDiff_const.mul
  exact (primitive_C1 (G.cost_diff s e).continuous).comp (by
    unfold edgeLoad
    apply ContDiff.sum
    intro r hr
    apply ContDiff.sum
    intro i hi
    exact (contDiff_apply_apply ℝ ℝ (t i) r).comp (contDiff_pi.mp contDiff_id i))

theorem coord_deriv (G : Game I T S E R) (q : (k : I) → T k → R → ℝ)
    (i : I) (ti : T i) (r : R) (t : (k : I) → T k) (k : I) (r' : R) :
    HasDerivAt (fun x => setCoord q i ti r x k (t k) r')
      (if k = i ∧ t i = ti ∧ r' = r then 1 else 0) (q i ti r) := by
  by_cases hk : k = i
  · subst k
    by_cases ht : t i = ti
    · by_cases hr : r' = r
      · subst r'
        convert! hasDerivAt_id (q i ti r) using 1 <;> simp [setCoord, ht]
        rfl
      · simpa [setCoord, ht, hr] using hasDerivAt_const (q i ti r) (q i ti r')
    · simpa [setCoord, ht] using hasDerivAt_const (q i ti r) (q i (t i) r')
  · simpa [setCoord, hk] using hasDerivAt_const (q i ti r) (q k (t k) r')

theorem load_coord_deriv (G : Game I T S E R) (q : (k : I) → T k → R → ℝ)
    (i : I) (ti : T i) (r : R) (e : E) (t : (k : I) → T k) :
    HasDerivAt (fun x => edgeLoad G (setCoord q i ti r x) e t)
      (if t i = ti ∧ e ∈ G.route r then 1 else 0) (q i ti r) := by
  have h := HasDerivAt.sum (u := Finset.univ.filter (fun r' => e ∈ G.route r'))
    (fun r' _ => HasDerivAt.sum (u := Finset.univ) (fun k _ => coord_deriv G q i ti r t k r'))
  convert! h using 1
  · ext x
    simp [edgeLoad]
  · by_cases ht : t i = ti
    · simp only [ht, true_and]
      simp_rw [show ∀ (k : I) (a : R), (if k = i ∧ a = r then (1 : ℝ) else 0) = if a = r then (if k = i then 1 else 0) else 0 by intros; split_ifs <;> simp_all]
      simp [Finset.sum_filter]
    · simp [ht]


theorem setCoord_self (q : (k : I) → T k → R → ℝ) (i : I) (ti : T i) (r : R) :
    setCoord q i ti r (q i ti r) = q := by
  simp [setCoord]

theorem potential_coord_deriv (G : Game I T S E R) (q : (k : I) → T k → R → ℝ)
    (i : I) (ti : T i) (r : R) :
    HasDerivAt (fun x => potential G (setCoord q i ti r x))
      (typeProb G i ti * expCost G q i ti r) (q i ti r) := by
  classical
  have h := HasDerivAt.sum (u := Finset.univ) (fun s _ =>
    HasDerivAt.sum (u := Finset.univ) (fun e _ =>
      HasDerivAt.sum (u := Finset.univ) (fun t _ =>
        ((primitive_deriv (G.cost_diff s e).continuous _).comp (q i ti r)
          (load_coord_deriv G q i ti r e t)).const_mul (G.prior s t))))
  simp only [setCoord_self] at h
  convert! h using 1
  · ext x
    simp [potential]
  · have hp : typeProb G i ti ≠ 0 := ne_of_gt (typeProb_pos G i ti)
    unfold expCost belief
    simp_rw [Finset.mul_sum]
    simp_rw [show ∀ s t e, typeProb G i ti * (G.prior s t / typeProb G i ti *
        G.cost s e (edgeLoad G q e t)) = G.prior s t * G.cost s e (edgeLoad G q e t) by
      intros; field_simp]
    apply Finset.sum_congr rfl
    intro s hs
    conv_rhs => rw [Finset.sum_comm]
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro t ht
    by_cases hti : t i = ti
    · simp only [hti, true_and, if_true, mul_ite, mul_one, mul_zero]
      rw [← Finset.sum_filter]
      simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
    · simp [hti]

end CBayes



open BayesRouting.VOI
open scoped ContDiff

namespace CBayes

variable {I : Type} [Fintype I] [DecidableEq I] {T : I → Type} [∀ i, Fintype (T i)]
  [∀ i, DecidableEq (T i)] [∀ i, Nonempty (T i)] {S E R : Type} [Fintype S] [Fintype E]
  [DecidableEq E] [Fintype R] [DecidableEq R] [Nonempty R]

theorem primitive_strictConvex (G : Game I T S E R) (s : S) (e : E) :
    StrictConvexOn ℝ Set.univ (fun y => ∫ z in (0 : ℝ)..y, G.cost s e z) := by
  apply StrictMono.strictConvexOn_univ_of_deriv (primitive_C1 (G.cost_diff s e).continuous).continuous
  have heq : deriv (fun y => ∫ z in (0 : ℝ)..y, G.cost s e z) = G.cost s e :=
    funext fun x => (primitive_deriv (G.cost_diff s e).continuous x).deriv
  rw [heq]
  exact G.cost_strictMono s e

theorem loadPotential_strict (G : Game I T S E R) :
    StrictConvexOn ℝ Set.univ (loadPotential G) := by
  classical
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  obtain ⟨e, t, hne⟩ : ∃ e t, x e t ≠ y e t := by
    by_contra! h
    exact hxy (funext fun e => funext fun t => h e t)
  obtain ⟨s, hs⟩ : ∃ s, 0 < G.prior s t := by
    by_contra! h
    exact (not_lt_of_ge (Finset.sum_nonpos fun s _ => h s)) (G.prior_full_support t)
  have hweak (s : S) (e : E) (t : (i : I) → T i) :
      G.prior s t * (∫ z in (0 : ℝ)..(a * x e t + b * y e t), G.cost s e z) ≤
      a * (G.prior s t * ∫ z in (0 : ℝ)..x e t, G.cost s e z) +
      b * (G.prior s t * ∫ z in (0 : ℝ)..y e t, G.cost s e z) := by
    have h := mul_le_mul_of_nonneg_left
      ((primitive_strictConvex G s e).convexOn.2 (Set.mem_univ (x e t)) (Set.mem_univ (y e t))
        ha.le hb.le hab) (G.prior_nonneg s t)
    dsimp only [smul_eq_mul] at h
    nlinarith
  have hstrict :
      G.prior s t * (∫ z in (0 : ℝ)..(a * x e t + b * y e t), G.cost s e z) <
      a * (G.prior s t * ∫ z in (0 : ℝ)..x e t, G.cost s e z) +
      b * (G.prior s t * ∫ z in (0 : ℝ)..y e t, G.cost s e z) := by
    have h := mul_lt_mul_of_pos_left
      ((primitive_strictConvex G s e).2 (Set.mem_univ (x e t)) (Set.mem_univ (y e t)) hne ha hb hab) hs
    dsimp only [smul_eq_mul] at h
    nlinarith
  simp only [loadPotential, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_lt_sum
  · intro s' _
    exact Finset.sum_le_sum fun e' _ => Finset.sum_le_sum fun t' _ => hweak s' e' t'
  · refine ⟨s, Finset.mem_univ _, Finset.sum_lt_sum ?_ ?_⟩
    · intro e' _
      exact Finset.sum_le_sum fun t' _ => hweak s e' t'
    · refine ⟨e, Finset.mem_univ _, Finset.sum_lt_sum ?_ ?_⟩
      · intro t' _
        exact hweak s e t'
      · exact ⟨t, Finset.mem_univ _, hstrict⟩

theorem loadPotential_C2 (G : Game I T S E R) (hc : ∀ s e, ContDiff ℝ 1 (G.cost s e)) :
    ContDiff ℝ 2 (loadPotential G) := by
  unfold loadPotential
  apply ContDiff.sum
  intro s hs
  apply ContDiff.sum
  intro e he
  apply ContDiff.sum
  intro t ht
  apply contDiff_const.mul
  exact (primitive_C2 (hc s e)).comp (contDiff_apply_apply ℝ ℝ e t)

end CBayes

theorem solution {I : Type} [Fintype I] [DecidableEq I] {T : I → Type} [∀ i, Fintype (T i)]
    [∀ i, DecidableEq (T i)] [∀ i, Nonempty (T i)] {S E R : Type} [Fintype S] [Fintype E]
    [DecidableEq E] [Fintype R] [Nonempty R]
    (G : Game I T S E R) :
    StrictConvexOn ℝ Set.univ (loadPotential G) ∧
      ((∀ s e, ContDiff ℝ 1 (G.cost s e)) → ContDiff ℝ 2 (loadPotential G)) := by
  classical
  exact ⟨CBayes.loadPotential_strict G, CBayes.loadPotential_C2 G⟩

