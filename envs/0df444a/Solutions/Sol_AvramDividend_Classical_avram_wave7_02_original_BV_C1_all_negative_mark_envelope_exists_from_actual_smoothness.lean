-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_original_BV_C1_all_negative_mark_envelope_exists_from_actual_smoothness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:16:26.870165+00:00
-- url     : https://prove2.me/submissions/04a658c5-c6a5-4950-a29c-e4c9fd48465c

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_C1_verification_candidate_uniform_below_finite_reserve_ceiling
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_original_bv_C1_band_derivative_lipschitz
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_C1_full_negative_source_mark_discounted_piecewise_variation_envelope
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Both the compact C1 first-variation constant and the global below-cap
large-mark value envelope are generated from true verification smoothness. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ v : ℝ, v < 0 → w v = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {v : ℝ | 0 < v ∧ ENNReal.ofReal v < C})
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (q : ℝ) (hq : 0 ≤ q) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b)
    (hOpen : IsOpen {v : ℝ | 0 < v ∧ ENNReal.ofReal v < C})
    (hBandSmooth : Icc (a / 2) b ⊆
      {v : ℝ | 0 < v ∧ ENNReal.ofReal v < C})
    (K : ℝ≥0)
    (hK : ∀ v ∈ Icc (a / 2) b, ‖deriv w v‖₊ ≤ K) :
    ∃ R : ℝ, 0 ≤ R ∧
      ∀ (ω : Ω) (t : ℝ≥0),
        Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s ω - rightLimit D s ω) t ∈ Icc a b →
        ∀ z : ℝ, z < 0 →
          |Real.exp (-(q * (t : ℝ))) *
            (w (Function.leftLim (fun s : ℝ≥0 =>
              x + X.X s ω - rightLimit D s ω) t + z) -
             w (Function.leftLim (fun s : ℝ≥0 =>
              x + X.X s ω - rightLimit D s ω) t))| ≤
            if z ≤ -a / 2 then 2 * R else (K : ℝ) * (-z) := by
  have hb : 0 ≤ b := by linarith only [ha, hab]
  obtain ⟨R, hR0, hBoundNorm⟩ :=
    avram_wave7_02_original_C1_verification_candidate_uniform_below_finite_reserve_ceiling
      w hw_cont hw_neg b hb
  have hBound : ∀ v : ℝ, v ≤ b → |w v| ≤ R := by
    intro v hv
    simpa only [Real.norm_eq_abs] using hBoundNorm v hv
  have hLip : ∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b,
      |w u - w v| ≤ (K : ℝ) * |u - v| :=
    avram_wave6_chat09_original_bv_C1_band_derivative_lipschitz
      X hBV C w (fun _ => hw_smooth) (a / 2) b
      hOpen hBandSmooth K hK
  refine ⟨R, hR0, ?_⟩
  intro ω t hBand z hz
  exact avram_wave7_02_original_C1_full_negative_source_mark_discounted_piecewise_variation_envelope
    X x D w q hq a b (K : ℝ) R ha hab
    (NNReal.coe_nonneg K) hR0 hLip hBound ω t hBand z hz
