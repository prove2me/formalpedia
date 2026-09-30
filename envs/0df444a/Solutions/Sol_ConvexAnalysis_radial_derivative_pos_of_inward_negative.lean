-- Prove2me | solution 1 for ConvexAnalysis.radial_derivative_pos_of_inward_negative
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-30T00:11:41.420296+00:00
-- url     : https://prove2.me/submissions/c348c3c5-d6c0-4644-9665-2f4cd742bee6

import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Basic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
open scoped Topology

/-- An inward-negative radial slice cannot have both a stationary boundary point
and a positive second derivative there. -/
theorem inward_negative_second_derivative_boundary_not_stationary (f : ℝ → ℝ)
    (hc : ContinuousAt f 1) (hzero : f 1 = 0)
    (hneg : ∀ t : ℝ, 0 ≤ t → t < 1 → f t < 0)
    (hsecond : 0 < deriv (deriv f) 1) : deriv f 1 ≠ 0 := by
  intro hstationary
  have hmin := isLocalMin_of_deriv_deriv_pos hsecond hstationary hc
  obtain ⟨ε, hε, hnear⟩ := Metric.eventually_nhds_iff.mp hmin
  let δ : ℝ := min (ε / 2) (1 / 2)
  have hδ : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδsmall : δ ≤ 1 / 2 := min_le_right _ _
  have hδε : δ < ε := (min_le_left _ _).trans_lt (by linarith)
  have hd : dist (1 - δ) (1 : ℝ) < ε := by
    rw [Real.dist_eq]
    have heq : (1 - δ) - 1 = -δ := by ring
    rw [heq, abs_neg, abs_of_pos hδ]
    exact hδε
  have hl := hnear hd
  have hn := hneg (1 - δ) (by linarith) (by linarith)
  rw [hzero] at hl
  linarith

theorem radial_slice_first_and_second_derivative (F : E → ℝ) (s : E)
    (hc : ContDiffAt ℝ 2 F s) :
    let f : ℝ → ℝ := fun t => F (t • s)
    deriv f 1 = fderiv ℝ F s s ∧
      deriv (deriv f) 1 = fderiv ℝ (fun x => fderiv ℝ F x s) s s := by
  let P : ℝ → E := fun t => t • s
  let f : ℝ → ℝ := F ∘ P
  let G : E → ℝ := fun x => fderiv ℝ F x s
  have hP (t : ℝ) : HasDerivAt P s t := by
    simpa only [P, id_eq, one_smul] using (hasDerivAt_id t).smul_const s
  have hPc : Continuous P := continuous_id.smul continuous_const
  have hP1 : P 1 = s := one_smul ℝ s
  have hFdiff : DifferentiableAt ℝ F s := hc.differentiableAt (by norm_num)
  have hf : HasDerivAt f (fderiv ℝ F s s) 1 :=
    hFdiff.hasFDerivAt.comp_hasDerivAt_of_eq 1 (hP 1) hP1.symm
  have hGc : ContDiffAt ℝ 1 G s :=
    (hc.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
  have hg : HasDerivAt (G ∘ P) (fderiv ℝ G s s) 1 :=
    hGc.differentiableAt_one.hasFDerivAt.comp_hasDerivAt_of_eq 1 (hP 1) hP1.symm
  have hPt : Filter.Tendsto P (nhds 1) (nhds s) := by
    have hPt' : Filter.Tendsto P (nhds 1) (nhds (P 1)) := hPc.continuousAt.tendsto
    simpa only [hP1] using hPt'
  have heq : deriv f =ᶠ[nhds 1] G ∘ P := by
    filter_upwards [hPt.eventually (hc.eventually (by norm_num))] with t ht
    exact (ht.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hP t) |>.deriv
  exact ⟨hf.deriv, (hg.congr_of_eventuallyEq heq).deriv⟩

theorem radial_transversality_from_tangential_curvature (F : E → ℝ) (s : E)
    (hsne : s ≠ 0) (hc : ContDiffAt ℝ 2 F s) (hzero : F s = 0)
    (hneg : ∀ t : ℝ, 0 ≤ t → t < 1 → F (t • s) < 0)
    (hcurv : ∀ v : E, v ≠ 0 → fderiv ℝ F s v = 0 →
      0 < fderiv ℝ (fun x => fderiv ℝ F x v) s v) :
    fderiv ℝ F s s ≠ 0 := by
  intro hstationary
  let f : ℝ → ℝ := fun t => F (t • s)
  obtain ⟨hfirst, hsecond⟩ := radial_slice_first_and_second_derivative F s hc
  have hpositive : 0 < deriv (deriv f) 1 := by
    rw [hsecond]
    exact hcurv s hsne hstationary
  have hfcont : ContinuousAt f 1 := by
    have hPcont : ContinuousAt (fun t : ℝ => t • s) 1 :=
      (continuous_id.smul continuous_const).continuousAt
    have hFcont : ContinuousAt F ((1 : ℝ) • s) := by
      simpa only [one_smul] using hc.continuousAt
    exact hFcont.comp (f := fun t : ℝ => t • s) hPcont
  have hfzero : f 1 = 0 := by simpa [f] using hzero
  have hnot := inward_negative_second_derivative_boundary_not_stationary f hfcont hfzero hneg hpositive
  rw [hfirst, hstationary] at hnot
  exact hnot rfl

theorem inward_negative_derivative_nonnegative (f : ℝ → ℝ) (d : ℝ)
    (hd : HasDerivAt f d 1) (hzero : f 1 = 0)
    (hneg : ∀ t : ℝ, 0 ≤ t → t < 1 → f t < 0) : 0 ≤ d := by
  have hmax : IsMaxOn f (Set.Icc (0 : ℝ) 1) 1 := by
    intro t ht
    change f t ≤ f 1
    rcases ht.2.eq_or_lt with he | hlt
    · rw [he]
    · rw [hzero]
      exact (hneg t ht.1 hlt).le
  have hseg : segment ℝ (1 : ℝ) 0 ⊆ Set.Icc 0 1 :=
    (convex_Icc (0 : ℝ) 1).segment_subset ⟨zero_le_one, le_rfl⟩ ⟨le_rfl, zero_le_one⟩
  have htangent := sub_mem_posTangentConeAt_of_segment_subset hseg
  have h := hmax.localize.hasFDerivWithinAt_nonpos
    hd.hasFDerivAt.hasFDerivWithinAt htangent
  simpa using h

theorem solution (F : E → ℝ) (s : E)
    (hsne : s ≠ 0) (hc : ContDiffAt ℝ 2 F s) (hzero : F s = 0)
    (hneg : ∀ t : ℝ, 0 ≤ t → t < 1 → F (t • s) < 0)
    (hcurv : ∀ v : E, v ≠ 0 → fderiv ℝ F s v = 0 →
      0 < fderiv ℝ (fun x => fderiv ℝ F x v) s v) :
    0 < fderiv ℝ F s s := by
  have hne := radial_transversality_from_tangential_curvature F s hsne hc hzero hneg hcurv
  have hP : HasDerivAt (fun t : ℝ => t • s) s 1 := by
    simpa only [id_eq, one_smul] using (hasDerivAt_id (1 : ℝ)).smul_const s
  have hf : HasDerivAt (fun t : ℝ => F (t • s)) (fderiv ℝ F s s) 1 :=
    (hc.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt_of_eq 1 hP
      (one_smul ℝ s).symm
  have hnonneg := inward_negative_derivative_nonnegative _ _ hf
    (by simpa only [one_smul] using hzero) hneg
  exact lt_of_le_of_ne hnonneg hne.symm
