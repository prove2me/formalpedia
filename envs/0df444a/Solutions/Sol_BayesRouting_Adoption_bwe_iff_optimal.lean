-- Prove2me | solution 1 for BayesRouting.Adoption.bwe_iff_optimal
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T14:46:05.735026+00:00
-- url     : https://prove2.me/submissions/f0f341b7-1484-4da7-aaca-836f58b3c42c

import Definitions.Def_BayesRouting_Adoption_Potential
import Definitions.Def_BayesRouting_VOI_Potential
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Algebra.BigOperators.Pi

section

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
end

section

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
end

section

open BayesRouting.VOI Finset
open scoped ContDiff

namespace CBayes

theorem finite_min_kkt {R : Type} [Fintype R] [Nonempty R] (w q : R → ℝ)
    (hq : ∀ r, 0 ≤ q r) (hopt : ∀ r, 0 < q r → ∀ r', w r ≤ w r') :
    let m := Finset.univ.inf' Finset.univ_nonempty w
    (∀ r, 0 ≤ w r - m) ∧ (∀ r, (w r - m) * q r = 0) := by
  classical
  dsimp only
  constructor
  · intro r
    exact sub_nonneg.mpr (Finset.inf'_le _ (Finset.mem_univ r))
  · intro r
    by_cases hr : q r = 0
    · simp [hr]
    · have hp : 0 < q r := lt_of_le_of_ne (hq r) (Ne.symm hr)
      have heq : w r = Finset.univ.inf' Finset.univ_nonempty w := le_antisymm
        (Finset.le_inf' _ _ fun r' _ => hopt r hp r')
        (Finset.inf'_le _ (Finset.mem_univ r))
      simp [heq]


variable {I : Type} [Fintype I] [DecidableEq I] {T : I → Type} [∀ i, Fintype (T i)]
  [∀ i, DecidableEq (T i)] [∀ i, Nonempty (T i)] {S E R : Type} [Fintype S] [Fintype E]
  [DecidableEq E] [Fintype R] [DecidableEq R] [Nonempty R]

def unit (i : I) (ti : T i) (r : R) : (k : I) → T k → R → ℝ :=
  Pi.single i (Pi.single ti (Pi.single r 1))

theorem setCoord_unit (q : (k : I) → T k → R → ℝ) (i : I) (ti : T i) (r : R) (x : ℝ) :
    setCoord q i ti r x = q + (x - q i ti r) • unit i ti r := by
  ext k tk r'
  by_cases hk : k = i
  · subst k
    by_cases ht : tk = ti
    · subst tk
      by_cases hr : r' = r
      · subst r'; simp [setCoord, unit]
      · simp [setCoord, unit, hr]
    · simp [setCoord, unit, ht]
  · simp [setCoord, unit, hk]

theorem differential_unit (G : Game I T S E R) (q : (k : I) → T k → R → ℝ)
    (i : I) (ti : T i) (r : R) :
    fderiv ℝ (potential G) q (unit i ti r) = typeProb G i ti * expCost G q i ti r := by
  have hline : HasDerivAt (fun x => q + (x - q i ti r) • unit i ti r) (unit i ti r) (q i ti r) := by
    simpa using (((hasDerivAt_id (q i ti r)).sub_const (q i ti r)).smul_const (unit i ti r)).const_add q
  have hd := ((potential_C1 G).differentiable (by norm_num) (q + (q i ti r - q i ti r) • unit i ti r)).hasFDerivAt.comp_hasDerivAt (q i ti r) hline
  simp only [sub_self, zero_smul, add_zero] at hd
  have hh := potential_coord_deriv G q i ti r
  simp_rw [setCoord_unit] at hh
  exact hd.unique hh

theorem differential_apply (G : Game I T S E R) (q v : (k : I) → T k → R → ℝ) :
    fderiv ℝ (potential G) q v =
      ∑ i, ∑ ti, ∑ r, (typeProb G i ti * expCost G q i ti r) * v i ti r := by
  have heq : v = ∑ i, ∑ ti, ∑ r, v i ti r • unit i ti r := by
    simp_rw [unit, ← Pi.single_smul, smul_eq_mul, mul_one]
    ext k tk r
    simp only [Finset.sum_apply]
    rw [Finset.sum_eq_single k]
    · simp only [Pi.single_eq_same]
      rw [Finset.sum_eq_single tk]
      · simp only [Pi.single_eq_same]
        rw [Finset.sum_eq_single r]
        · simp
        · intro r' hr' hne
          simp [hne, Ne.symm hne]
        · simp
      · intro tk' htk' hne
        simp [hne, Ne.symm hne]
      · simp
    · intro k' hk' hne
      simp [hne, Ne.symm hne]
    · simp
  conv_lhs => rw [heq]
  simp_rw [map_sum, map_smul, differential_unit, smul_eq_mul, mul_comm]

theorem feasible_convex (G : Game I T S E R) (lam : I → ℝ) :
    Convex ℝ (feasibleStrategies G lam) := by
  intro x hx y hy a b ha hb hab
  constructor
  · intro i ti
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hx.1 i ti, hy.1 i ti]
    rw [← add_mul, hab, one_mul]
  · intro i ti r
    exact add_nonneg (mul_nonneg ha (hx.2 i ti r)) (mul_nonneg hb (hy.2 i ti r))

theorem edgeLoad_mix (G : Game I T S E R) (q q' : (k : I) → T k → R → ℝ) (a b : ℝ) :
    edgeLoad G (a • q + b • q') = a • edgeLoad G q + b • edgeLoad G q' := by
  ext e t
  simp [edgeLoad, Finset.sum_add_distrib, Finset.mul_sum]

theorem potential_convex (G : Game I T S E R) : ConvexOn ℝ Set.univ (potential G) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have h := (loadPotential_strict G).convexOn.2 (Set.mem_univ (edgeLoad G x))
    (Set.mem_univ (edgeLoad G y)) ha hb hab
  rw [← edgeLoad_mix] at h
  exact h

theorem supporting {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : V → ℝ) (hc : ConvexOn ℝ Set.univ F) (hd : Differentiable ℝ F) (x y : V) :
    fderiv ℝ F x (y - x) ≤ F y - F x := by
  have hline : HasDerivAt (fun t : ℝ => x + t • (y-x)) (y-x) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (y-x)).const_add x
  have hder := (hd (x+(0:ℝ) • (y-x))).hasFDerivAt.comp_hasDerivAt (0:ℝ) hline
  simp only [zero_smul, add_zero] at hder
  have hc' : ConvexOn ℝ Set.univ (fun t : ℝ => F (x+t • (y-x))) := by
    simpa [Function.comp_def, AffineMap.lineMap_apply_module', add_comm] using
      hc.comp_affineMap (AffineMap.lineMap (k := ℝ) x y)
  have h := hc'.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) (by norm_num) hder
  simpa [slope_def_field] using h


theorem optimal_of_bwe (G : Game I T S E R) (lam : I → ℝ)
    (q : (k : I) → T k → R → ℝ) (hq : IsBWE G lam q)
    (q' : (k : I) → T k → R → ℝ) (hq' : q' ∈ feasibleStrategies G lam) :
    potential G q ≤ potential G q' := by
  have hd := supporting (potential G) (potential_convex G)
    ((potential_C1 G).differentiable (by norm_num)) q q'
  suffices hnon : 0 ≤ fderiv ℝ (potential G) q (q' - q) by linarith
  rw [differential_apply]
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro ti hti
  let w : R → ℝ := fun r => typeProb G i ti * expCost G q i ti r
  let m := Finset.univ.inf' Finset.univ_nonempty w
  have hm := finite_min_kkt w (q i ti) (hq.1.2 i ti)
    (fun r hr r' => mul_le_mul_of_nonneg_left (hq.2 i ti r hr r') (typeProb_pos G i ti).le)
  have hsum : ∑ r, (q' i ti r - q i ti r) = 0 := by
    rw [Finset.sum_sub_distrib, hq'.1 i ti, hq.1.1 i ti, sub_self]
  have hnon : 0 ≤ ∑ r, (w r - m) * (q' i ti r - q i ti r) := by
    apply Finset.sum_nonneg
    intro r hr
    have hn := mul_nonneg (hm.1 r) (hq'.2 i ti r)
    have hz := hm.2 r
    dsimp only [m] at *
    nlinarith
  have heq : (∑ r, (w r - m) * (q' i ti r - q i ti r)) =
      ∑ r, w r * (q' i ti r - q i ti r) := by
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum, mul_zero, sub_zero]
  rw [heq] at hnon
  exact hnon

theorem transfer_feasible (G : Game I T S E R) (lam : I → ℝ)
    (q : (k : I) → T k → R → ℝ) (hq : q ∈ feasibleStrategies G lam)
    (i : I) (ti : T i) (r r' : R) :
    q + q i ti r • (unit i ti r' - unit i ti r) ∈ feasibleStrategies G lam := by
  by_cases heq : r = r'
  · subst r'; simpa using hq
  constructor
  · intro k tk
    by_cases hk : k = i
    · subst k
      by_cases ht : tk = ti
      · subst tk
        simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
          Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
        simp [unit, Pi.single, Function.update_apply, hq.1 i ti]
      · simpa [unit, ht] using hq.1 i tk
    · simpa [unit, hk] using hq.1 k tk
  · intro k tk r0
    by_cases hk : k = i
    · subst k
      by_cases ht : tk = ti
      · subst tk
        by_cases hr : r0 = r
        · subst r0; simp [unit, heq]
        · by_cases hr' : r0 = r'
          · subst r0; simpa [unit, heq, Ne.symm heq] using add_nonneg (hq.2 i ti r') (hq.2 i ti r)
          · simpa [unit, hr, hr'] using hq.2 i ti r0
      · simpa [unit, ht] using hq.2 i tk r0
    · simpa [unit, hk] using hq.2 k tk r0

theorem bwe_of_optimal (G : Game I T S E R) (lam : I → ℝ)
    (q : (k : I) → T k → R → ℝ) (hq : q ∈ feasibleStrategies G lam)
    (hopt : ∀ q' ∈ feasibleStrategies G lam, potential G q ≤ potential G q') :
    IsBWE G lam q := by
  refine ⟨hq, ?_⟩
  intro i ti r hr r'
  let q' := q + q i ti r • (unit i ti r' - unit i ti r)
  have hq' : q' ∈ feasibleStrategies G lam := transfer_feasible G lam q hq i ti r r'
  have hmin : IsLocalMinOn (potential G) (feasibleStrategies G lam) q :=
    (show IsMinOn (potential G) (feasibleStrategies G lam) q from hopt).localize
  have hnon := hmin.hasFDerivWithinAt_nonneg
    (((potential_C1 G).differentiable (by norm_num) q).hasFDerivAt.hasFDerivWithinAt)
    (sub_mem_posTangentConeAt_of_segment_subset ((feasible_convex G lam).segment_subset hq hq'))
  dsimp [q'] at hnon
  simp only [add_sub_cancel_left, map_smul, map_sub, differential_unit, smul_eq_mul] at hnon
  have hcost := (mul_nonneg_iff_of_pos_left hr).mp hnon
  rw [← mul_sub] at hcost
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left (typeProb_pos G i ti)).mp hcost)


theorem optimal_load_unique (G : Game I T S E R) (lam : I → ℝ)
    (q q' : (k : I) → T k → R → ℝ) (hq : IsBWE G lam q) (hq' : IsBWE G lam q') :
    edgeLoad G q = edgeLoad G q' := by
  by_contra hne
  have hstrict := (loadPotential_strict G).2 (Set.mem_univ (edgeLoad G q))
    (Set.mem_univ (edgeLoad G q')) hne
    (by norm_num : 0 < (1/2 : ℝ)) (by norm_num : 0 < (1/2 : ℝ)) (by norm_num)
  rw [← edgeLoad_mix] at hstrict
  change potential G ((1/2 : ℝ) • q + (1/2 : ℝ) • q') <
    (1/2 : ℝ) * potential G q + (1/2 : ℝ) * potential G q' at hstrict
  have hmid := (feasible_convex G lam) hq.1 hq'.1 (by norm_num : 0 ≤ (1/2 : ℝ))
    (by norm_num : 0 ≤ (1/2 : ℝ)) (by norm_num : (1/2 : ℝ)+(1/2 : ℝ)=1)
  have h1 := optimal_of_bwe G lam q hq _ hmid
  have h2 := optimal_of_bwe G lam q hq q' hq'.1
  have h3 := optimal_of_bwe G lam q' hq' q hq.1
  linarith


theorem equilibrium_iff (G : Game I T S E R) (lam : I → ℝ) :
    (∀ q : (i : I) → T i → R → ℝ, IsBWE G lam q ↔
        (q ∈ feasibleStrategies G lam ∧
          ∀ q' ∈ feasibleStrategies G lam, potential G q ≤ potential G q')) ∧
      ∀ q q' : (i : I) → T i → R → ℝ, IsBWE G lam q → IsBWE G lam q' →
        edgeLoad G q = edgeLoad G q' := by
  refine ⟨fun q => ⟨fun hq => ⟨hq.1, optimal_of_bwe G lam q hq⟩,
    fun hq => bwe_of_optimal G lam q hq.1 hq.2⟩, ?_⟩
  exact fun q q' hq hq' => optimal_load_unique G lam q q' hq hq'

end CBayes
end

open BayesRouting.Adoption

theorem solution {I : Type} [Fintype I] [DecidableEq I] {T : I → Type} [∀ i, Fintype (T i)]
    [∀ i, DecidableEq (T i)] [∀ i, Nonempty (T i)] {S E R : Type} [Fintype S] [Fintype E]
    [DecidableEq E] [Fintype R] [Nonempty R]
    (G : Game I T S E R) (lam : I → ℝ) (hlam : lam ∈ stdSimplex ℝ I) :
    (∀ q, IsBWE G lam q ↔
      (q ∈ feasibleStrategies G lam ∧
        ∀ q' ∈ feasibleStrategies G lam, potential G q ≤ potential G q')) ∧
    (∀ q q', IsBWE G lam q → IsBWE G lam q' → edgeLoad G q = edgeLoad G q') := by
  classical
  let G' : BayesRouting.VOI.Game I T S E R :=
    { prior := G.prior
      cost := G.cost
      route := G.route
      D := G.D
      prior_nonneg := G.prior_nonneg
      prior_sum_one := G.prior_sum_one
      prior_full_support := G.prior_full_support
      D_pos := G.D_pos
      cost_pos := G.cost_pos
      cost_strictMono := G.cost_strictMono
      cost_diff := G.cost_diff }
  exact CBayes.equilibrium_iff G' lam

