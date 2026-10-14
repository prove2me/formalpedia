-- Prove2me | solution 1 for DbarRegularity.eLpNorm_le_eLpNorm_fderiv_one_of_tsupport_subset_ball_center
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-13T15:25:43.484932+00:00
-- url     : https://prove2.me/submissions/44bf9d50-c384-4ec3-8be4-82ac27d0a392

import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.FDeriv.Const
import Theorems.Thm_DbarRegularity_eLpNorm_le_eLpNorm_fderiv_one_of_tsupport_subset_ball



namespace DbarRegularity

open MeasureTheory Metric

/-- `L^p` Poincaré inequality in the real direction on a disc `B_R(c)` with arbitrary centre:
`‖φ‖_{L^p} ≤ 2R ‖∂φ/∂s‖_{L^p}` for `C¹` maps `φ : ℂ → E` with support in `B_R(c)`. -/
theorem eLpNorm_le_eLpNorm_fderiv_one_of_tsupport_subset_ball_center_aux {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (c : ℂ) (R p : ℝ) (hp : 1 ≤ p)
    (φ : ℂ → E) (hφ : ContDiff ℝ 1 φ) (hsupp : tsupport φ ⊆ ball c R) :
    eLpNorm φ (ENNReal.ofReal p) volume
      ≤ ENNReal.ofReal (2 * R) * eLpNorm (fun z => fderiv ℝ φ z 1) (ENNReal.ofReal p) volume := by
  set ψ : ℂ → E := fun z => φ (z + c) with hψdef
  have hψ : ContDiff ℝ 1 ψ := hφ.comp (contDiff_id.add contDiff_const)
  have hsψ : tsupport ψ ⊆ ball 0 R := by
    intro z hz
    have h1 : tsupport ψ ⊆ (fun z => z + c) ⁻¹' tsupport φ :=
      tsupport_comp_subset_preimage φ (continuous_add_right c)
    have h2 := hsupp (h1 hz)
    simpa [mem_ball, dist_eq_norm] using h2
  have h := eLpNorm_le_eLpNorm_fderiv_one_of_tsupport_subset_ball R p hp ψ hψ hsψ
  have hm : MeasurePreserving (fun z : ℂ => z + c) volume volume :=
    measurePreserving_add_right volume c
  have e1 : eLpNorm ψ (ENNReal.ofReal p) volume = eLpNorm φ (ENNReal.ofReal p) volume :=
    eLpNorm_comp_measurePreserving hφ.continuous.aestronglyMeasurable hm
  have hcont : Continuous (fun z => fderiv ℝ φ z 1) :=
    (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have e2 : eLpNorm (fun z => fderiv ℝ ψ z 1) (ENNReal.ofReal p) volume
      = eLpNorm (fun z => fderiv ℝ φ z 1) (ENNReal.ofReal p) volume := by
    have : (fun z => fderiv ℝ ψ z 1) = (fun z => fderiv ℝ φ z 1) ∘ (fun z : ℂ => z + c) := by
      funext z
      simp only [hψdef, Function.comp_apply]
      rw [fderiv_comp_add_right]
    rw [this]
    exact eLpNorm_comp_measurePreserving hcont.aestronglyMeasurable hm
  rw [← e1, ← e2]
  exact h

end DbarRegularity

open DbarRegularity

open MeasureTheory Metric

theorem solution {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (c : ℂ) (R p : ℝ) (hp : 1 ≤ p)
    (φ : ℂ → E) (hφ : ContDiff ℝ 1 φ) (hsupp : tsupport φ ⊆ ball c R) :
    eLpNorm φ (ENNReal.ofReal p) volume
      ≤ ENNReal.ofReal (2 * R) * eLpNorm (fun z => fderiv ℝ φ z 1) (ENNReal.ofReal p) volume :=
  eLpNorm_le_eLpNorm_fderiv_one_of_tsupport_subset_ball_center_aux c R p hp φ hφ hsupp
