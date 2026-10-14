-- Prove2me | solution 1 for DbarRegularity.eLpNorm_le_eLpNorm_fderiv_one_of_tsupport_subset_ball
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T23:40:49.6127+00:00
-- url     : https://prove2.me/submissions/74b49b8c-dd91-4e96-bc5b-38a00506f422

import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.RealDeriv
import Theorems.Thm_DbarRegularity_eLpNorm_le_eLpNorm_deriv_of_tsupport_subset_ball



namespace DbarRegularity

open MeasureTheory Metric Set
open scoped ENNReal

/-- `L^p` Poincaré inequality in the real direction on the plane: for real `p ≥ 1`, a `C¹` map
`φ : ℂ → E` with support in the disc `B_R(0)` satisfies `‖φ‖_{L^p} ≤ 2R ‖φ_s‖_{L^p}`, where
`φ_s = fderiv ℝ φ z 1`. -/
theorem eLpNorm_le_eLpNorm_fderiv_one_of_tsupport_subset_ball_aux {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (R p : ℝ) (hp : 1 ≤ p)
    (φ : ℂ → E) (hφ : ContDiff ℝ 1 φ) (hsupp : tsupport φ ⊆ ball 0 R) :
    eLpNorm φ (ENNReal.ofReal p) volume
      ≤ ENNReal.ofReal (2 * R) * eLpNorm (fun z => fderiv ℝ φ z 1) (ENNReal.ofReal p) volume := by
  set P : ℝ≥0∞ := ENNReal.ofReal p with hP
  have hp0 : 0 < p := by linarith
  have hPr : P.toReal = p := ENNReal.toReal_ofReal hp0.le
  have hP0 : P ≠ 0 := by rw [hP]; simp; linarith
  have hPt : P ≠ ⊤ := ENNReal.ofReal_ne_top
  set a : ℝ≥0∞ := ENNReal.ofReal (2 * R) with ha
  -- the power form of the one-dimensional inequality
  have h1D : ∀ g : ℝ → E, ContDiff ℝ 1 g → tsupport g ⊆ ball 0 R →
      ∫⁻ x, ‖g x‖ₑ ^ p ≤ a ^ p * ∫⁻ x, ‖deriv g x‖ₑ ^ p := by
    intro g hg hgs
    have h := eLpNorm_le_eLpNorm_deriv_of_tsupport_subset_ball R p hp g hg hgs
    rw [eLpNorm_eq_lintegral_rpow_enorm hP0 hPt, eLpNorm_eq_lintegral_rpow_enorm hP0 hPt,
      hPr] at h
    have h' := ENNReal.rpow_le_rpow h hp0.le
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, one_div, ENNReal.rpow_inv_rpow hp0.ne',
      ENNReal.rpow_inv_rpow hp0.ne'] at h'
    exact h'
  -- the power form on the plane
  have hmain : ∫⁻ z, ‖φ z‖ₑ ^ p ≤ a ^ p * ∫⁻ z, ‖fderiv ℝ φ z 1‖ₑ ^ p := by
    set e := Complex.measurableEquivRealProd
    have hmp : MeasurePreserving e.symm (volume.prod volume) volume :=
      Complex.volume_preserving_equiv_real_prod.symm
    have hsym : ∀ q : ℝ × ℝ, e.symm q = (q.1 : ℂ) + (q.2 : ℂ) * Complex.I := by
      intro q; apply Complex.ext <;> simp [e, Complex.measurableEquivRealProd_symm_apply]
    have hc := hφ.continuous_fderiv (by norm_num)
    have hFm : Measurable fun z => ‖φ z‖ₑ ^ p :=
      ((ENNReal.continuous_rpow_const (y := p)).comp hφ.continuous.enorm).measurable
    have hHm : Measurable fun z => ‖fderiv ℝ φ z 1‖ₑ ^ p :=
      ((ENNReal.continuous_rpow_const (y := p)).comp
        (by fun_prop : Continuous fun z => fderiv ℝ φ z 1).enorm).measurable
    rw [← hmp.lintegral_comp_emb e.symm.measurableEmbedding (fun z => ‖φ z‖ₑ ^ p),
      ← hmp.lintegral_comp_emb e.symm.measurableEmbedding (fun z => ‖fderiv ℝ φ z 1‖ₑ ^ p)]
    rw [lintegral_prod_symm (fun q => ‖φ (e.symm q)‖ₑ ^ p)
        (hFm.comp e.symm.measurable).aemeasurable,
      lintegral_prod_symm (fun q => ‖fderiv ℝ φ (e.symm q) 1‖ₑ ^ p)
        (hHm.comp e.symm.measurable).aemeasurable,
      ← lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp0.le ENNReal.ofReal_ne_top)]
    refine lintegral_mono fun t => ?_
    simp only [hsym]
    set c : ℝ → ℂ := fun s => (s : ℂ) + (t : ℂ) * Complex.I
    have hcC : ContDiff ℝ 1 c := ContDiff.add Complex.ofRealCLM.contDiff contDiff_const
    have hcd : ∀ s, HasDerivAt c 1 s := fun s => by
      have := ((hasDerivAt_id s).ofReal_comp).add_const ((t : ℂ) * Complex.I)
      convert this using 1 <;> first | rfl | simp [c]
    have hsl : ContDiff ℝ 1 (φ ∘ c) := hφ.comp hcC
    have hslsupp : tsupport (φ ∘ c) ⊆ ball 0 R := by
      refine (tsupport_comp_subset_preimage φ hcC.continuous).trans fun s hs => ?_
      have := hsupp hs
      rw [mem_ball, dist_zero_right] at this ⊢
      calc ‖s‖ = |(c s).re| := by simp [c]
        _ ≤ ‖c s‖ := Complex.abs_re_le_norm _
        _ < R := this
    have hderiv : ∀ s, deriv (φ ∘ c) s = fderiv ℝ φ (c s) 1 := fun s =>
      (((hφ.differentiable one_ne_zero) (c s)).hasFDerivAt.comp_hasDerivAt s (hcd s)).deriv
    have := h1D (φ ∘ c) hsl hslsupp
    simp only [hderiv, Function.comp] at this
    exact this
  rw [eLpNorm_eq_lintegral_rpow_enorm hP0 hPt, eLpNorm_eq_lintegral_rpow_enorm hP0 hPt, hPr]
  calc (∫⁻ z, ‖φ z‖ₑ ^ p) ^ (1 / p)
      ≤ (a ^ p * ∫⁻ z, ‖fderiv ℝ φ z 1‖ₑ ^ p) ^ (1 / p) :=
        ENNReal.rpow_le_rpow hmain (by positivity)
    _ = a * (∫⁻ z, ‖fderiv ℝ φ z 1‖ₑ ^ p) ^ (1 / p) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), one_div,
          ENNReal.rpow_rpow_inv hp0.ne']

end DbarRegularity

open DbarRegularity

open MeasureTheory Metric Set
open scoped ENNReal

theorem solution {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (R p : ℝ) (hp : 1 ≤ p)
    (φ : ℂ → E) (hφ : ContDiff ℝ 1 φ) (hsupp : tsupport φ ⊆ ball 0 R) :
    eLpNorm φ (ENNReal.ofReal p) volume
      ≤ ENNReal.ofReal (2 * R) * eLpNorm (fun z => fderiv ℝ φ z 1) (ENNReal.ofReal p) volume :=
  eLpNorm_le_eLpNorm_fderiv_one_of_tsupport_subset_ball_aux R p hp φ hφ hsupp
