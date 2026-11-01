-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05a_scale_primitive_residual_eq_one_of_laplace
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T14:39:01.315423+00:00
-- url     : https://prove2.me/submissions/7377c61d-4857-4904-88f1-643420ba1217

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_laplace_ae_zero_of_signed_20261026
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p3_generator_residual_continuousOn_compact_of_monotone_global_C2
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_source_scale_primitive_global_monotone
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_scale_primitive_zero_nonpositive
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_scale_primitive_contDiffOn_two_of_standing
import Theorems.Thm_AvramDividend_Classical_scaleFunction_monotone
import Theorems.Thm_AvramDividend_Classical_chat04_scale_zero_origin_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_scaleFunction_continuous_of_zero_origin

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set intervalIntegral Filter
open scoped NNReal ENNReal

set_option maxHeartbeats 1000000

/-- Source primitive residual identified pointwise from its positive-axis Laplace family,
    using genuine compensated-generator continuity on compact reserves. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (b : ℝ) (hb : 0 < b)
    (hLap : ∀ θ : ℝ, b < θ →
      IntegrableOn
        (fun x : ℝ => Real.exp (-(θ*x)) *
          (X.generator (fun z : ℝ => ∫ t in (0 : ℝ)..z, W t) x -
            q * (∫ t in (0 : ℝ)..x, W t)))
        (Ioi (0 : ℝ)) volume ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ*x)) *
        (X.generator (fun z : ℝ => ∫ t in (0 : ℝ)..z, W t) x -
          q * (∫ t in (0 : ℝ)..x, W t))) = 1 / θ) :
    ∀ x : ℝ, 0 < x →
      X.generator (fun z : ℝ => ∫ t in (0 : ℝ)..z, W t) x -
        q * (∫ t in (0 : ℝ)..x, W t) = 1 := by
  let U : ℝ → ℝ := fun z => ∫ t in (0 : ℝ)..z, W t
  let R : ℝ → ℝ := fun z => X.generator U z - q * U z - 1
  have hLapR : ∀ θ : ℝ, b < θ →
      IntegrableOn (fun x : ℝ => Real.exp (-(θ*x)) * R x)
        (Ioi (0 : ℝ)) volume ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ*x)) * R x) = 0 := by
    intro θ hθ
    have hθpos : 0 < θ := hb.trans hθ
    have hθneg : -θ < 0 := neg_neg_of_pos hθpos
    have hEint :
        IntegrableOn (fun x : ℝ => Real.exp (-(θ*x))) (Ioi (0 : ℝ)) volume := by
      simpa only [neg_mul] using (integrableOn_exp_mul_Ioi hθneg 0)
    have hEeq :
        (∫ x in Ioi (0 : ℝ), Real.exp (-(θ*x))) = 1 / θ := by
      simpa [neg_mul] using (integral_exp_mul_Ioi hθneg (0 : ℝ))
    have hL := hLap θ hθ
    have heq :
        (fun x : ℝ => Real.exp (-(θ*x)) * R x) =
        (fun x : ℝ => Real.exp (-(θ*x)) *
          (X.generator U x - q * U x) - Real.exp (-(θ*x))) := by
      funext x
      dsimp [R]
      ring
    rw [heq]
    constructor
    · exact hL.1.sub hEint
    · rw [integral_sub hL.1 hEint]
      rw [hL.2, hEeq]
      ring
  have haeR : ∀ᵐ z ∂((volume : Measure ℝ).restrict (Ioi (0 : ℝ))), R z = 0 :=
    avram_laplace_ae_zero_of_signed_20261026 R b hLapR
  have hWmono : Monotone W := scaleFunction_monotone X q W hW
  have hWzero : W 0 = 0 :=
    chat04_scale_zero_origin_of_unbounded_variation X hnbv q hq W hW
  have hWcont : Continuous W :=
    scaleFunction_continuous_of_zero_origin X q W hW hWzero
  have hUmono : Monotone U :=
    avram_wave4_p2_source_scale_primitive_global_monotone X q W hW
  have hUcont : Continuous U := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact (intervalIntegral.integral_hasDerivAt_right
      (hWcont.intervalIntegrable 0 z)
      (hWcont.stronglyMeasurableAtFilter volume (nhds z))
      hWcont.continuousAt).continuousAt
  have hUnonneg : ∀ z : ℝ, 0 ≤ U z := by
    intro z
    by_cases hz : z ≤ 0
    · have heq : U z = 0 :=
        avram_wave4_p2_scale_primitive_zero_nonpositive X q W hW z hz
      rw [heq]
    · exact le_trans (by
        simp [U]) (hUmono (le_of_lt (lt_of_not_ge hz)))
  have hUC2global : ContDiffOn ℝ 2 U (Ioi (0 : ℝ)) :=
    avram_wave4_p2_scale_primitive_contDiffOn_two_of_standing
      X hX q hq W hW
  intro x hx
  let a : ℝ := x + 1
  have hxa : x < a := by dsimp [a]; linarith
  have hUC2 : ContDiffOn ℝ 2 U (Ioo 0 a) :=
    hUC2global.mono (fun z hz => hz.1)
  let l : ℝ := x / 2
  let u : ℝ := (x + a) / 2
  have hl : 0 < l := by dsimp [l]; linarith [hx]
  have hxl : l < x := by dsimp [l]; linarith [hx]
  have hxu : x < u := by dsimp [u]; linarith [hxa]
  have hu : u < a := by dsimp [u]; linarith [hxa]
  have hlu : l < u := hxl.trans hxu
  have hxlu : x ∈ Ioo l u := ⟨hxl, hxu⟩
  have hRcontIcc : ContinuousOn (fun z => X.generator U z - q * U z) (Icc l u) :=
    avram_wave4_p3_generator_residual_continuousOn_compact_of_monotone_global_C2
      X q U hUnonneg hUmono hUcont a l u hl hlu hu hUC2
  have hRcont : ContinuousOn R (Ioo l u) := by
    change ContinuousOn (fun z => (X.generator U z - q * U z) - 1) (Ioo l u)
    exact (hRcontIcc.mono (fun z hz => ⟨hz.1.le, hz.2.le⟩)).sub continuousOn_const
  have haeLocal : ∀ᵐ z ∂((volume : Measure ℝ).restrict (Ioo l u)), R z = 0 := by
    apply MeasureTheory.ae_restrict_of_ae_restrict_of_subset
      (show Ioo l u ⊆ Ioi (0 : ℝ) from
        fun z hz => hl.trans hz.1)
    exact haeR
  have hclosure : Ioo l u ⊆ closure (interior (Ioo l u)) := by
    simpa [isOpen_Ioo.interior_eq] using
      (subset_closure : Ioo l u ⊆ closure (Ioo l u))
  have hEqOn : EqOn R (fun _ : ℝ => (0 : ℝ)) (Ioo l u) :=
    MeasureTheory.Measure.eqOn_of_ae_eq
      haeLocal hRcont continuousOn_const hclosure
  have hRx := hEqOn hxlu
  dsimp [R, U] at hRx ⊢
  linarith
