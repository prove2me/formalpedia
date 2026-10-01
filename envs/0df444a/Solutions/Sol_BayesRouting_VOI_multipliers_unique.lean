-- Prove2me | solution 1 for BayesRouting.VOI.multipliers_unique
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T14:36:50.184312+00:00
-- url     : https://prove2.me/submissions/2a1a2f70-5542-4674-a36f-8b30d59fc309

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



open BayesRouting.VOI Finset

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

theorem finite_min_unique {R : Type} [Fintype R] [Nonempty R] (w q : R → ℝ)
    (hpos : ∃ r, 0 < q r) (μ : ℝ) (ν : R → ℝ)
    (hstat : ∀ r, w r = μ + ν r) (hnon : ∀ r, 0 ≤ ν r) (hcomp : ∀ r, ν r * q r = 0) :
    μ = Finset.univ.inf' Finset.univ_nonempty w ∧
      ∀ r, ν r = w r - Finset.univ.inf' Finset.univ_nonempty w := by
  classical
  obtain ⟨r, hr⟩ := hpos
  have hn : ν r = 0 := (mul_eq_zero.mp (hcomp r)).resolve_right hr.ne'
  have heq : μ = Finset.univ.inf' Finset.univ_nonempty w := by
    apply le_antisymm
    · apply Finset.le_inf'
      intro r' _
      linarith [hstat r', hnon r']
    · have hi := Finset.inf'_le w (Finset.mem_univ r)
      linarith [hstat r]
  exact ⟨heq, fun r => by rw [← heq]; linarith [hstat r]⟩

end CBayes

theorem solution {I : Type} [Fintype I] [DecidableEq I] {T : I → Type} [∀ i, Fintype (T i)]
    [∀ i, DecidableEq (T i)] [∀ i, Nonempty (T i)] {S E R : Type} [Fintype S] [Fintype E]
    [DecidableEq E] [Fintype R] [DecidableEq R] [Nonempty R]
    (G : Game I T S E R) (lam : I → ℝ) (hlam : lam ∈ stdSimplex ℝ I)
    (q : (i : I) → T i → R → ℝ) (hq : IsBWE G lam q) :
    let μstar : (i : I) → T i → ℝ := fun i ti =>
      univ.inf' univ_nonempty (fun r => typeProb G i ti * expCost G q i ti r)
    let νstar : (i : I) → T i → R → ℝ := fun i ti r =>
      typeProb G i ti * expCost G q i ti r - μstar i ti
    let IsKKT : ((i : I) → T i → ℝ) → ((i : I) → T i → R → ℝ) → Prop := fun μ ν =>
      (∀ i ti r, HasDerivAt (fun x => potential G (setCoord q i ti r x))
          (μ i ti + ν i ti r) (q i ti r)) ∧
        (∀ i ti r, 0 ≤ ν i ti r) ∧ (∀ i ti r, ν i ti r * q i ti r = 0)
    IsKKT μstar νstar ∧
      ∀ μ ν, IsKKT μ ν → ∀ i, 0 < lam i → ∀ ti,
        μ i ti = μstar i ti ∧ ∀ r, ν i ti r = νstar i ti r := by
  classical
  dsimp only
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · intro i ti r
      convert! CBayes.potential_coord_deriv G q i ti r using 1 <;> ring
    · intro i ti r
      exact (CBayes.finite_min_kkt _ (q i ti) (hq.1.2 i ti)
        (fun r hr r' => mul_le_mul_of_nonneg_left (hq.2 i ti r hr r')
          (CBayes.typeProb_pos G i ti).le)).1 r
    · intro i ti r
      exact (CBayes.finite_min_kkt _ (q i ti) (hq.1.2 i ti)
        (fun r hr r' => mul_le_mul_of_nonneg_left (hq.2 i ti r hr r')
          (CBayes.typeProb_pos G i ti).le)).2 r
  · intro μ ν hk i hi ti
    have hpos : ∃ r, 0 < q i ti r := by
      by_contra! h
      have hh := Finset.sum_nonpos (s := Finset.univ) (fun r _ => h r)
      rw [hq.1.1 i ti] at hh
      exact (not_le_of_gt (mul_pos hi G.D_pos)) hh
    apply CBayes.finite_min_unique _ (q i ti) hpos (μ i ti) (ν i ti)
    · intro r
      exact (CBayes.potential_coord_deriv G q i ti r).unique (hk.1 i ti r)
    · exact hk.2.1 i ti
    · exact hk.2.2 i ti

