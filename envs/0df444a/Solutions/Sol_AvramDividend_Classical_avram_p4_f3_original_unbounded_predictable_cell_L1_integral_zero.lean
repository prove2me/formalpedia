-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_unbounded_predictable_cell_L1_integral_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T13:10:45.270107+00:00
-- url     : https://prove2.me/submissions/bd984bcd-bacf-46a7-92c3-dedf38e1b178

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_unbounded_predictable_negative_cell_condExp_auto
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_negative_borel_cell_centred_L2_from_full_band
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original weighted physical compensated cell is integrable with zero mean. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (n : ℕ)
    (s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T)
    (ε : ℝ) (hε : 0 < ε) (B : Set ℝ)
    (hB : MeasurableSet B) (hBand : B ⊆ Ioo (-1 : ℝ) (-ε))
    (hCut : B ⊆ Iic (-(1 / ((n : ℝ) + 1))))
    (H : Ω → ℝ) (hH : StronglyMeasurable[𝓕 s] H)
    (hHL2 : MemLp H 2 P) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)
    let r : ℝ := (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal
    Integrable (fun ω => H ω * ((N ω).toReal - r)) P ∧
      ∫ ω, H ω * ((N ω).toReal - r) ∂P = 0 := by
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ B)
  let r : ℝ := (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal
  change Integrable (fun ω => H ω * ((N ω).toReal - r)) P ∧
    ∫ ω, H ω * ((N ω).toReal - r) ∂P = 0
  have hCountL2 : MemLp (fun ω => (N ω).toReal - r) 2 P :=
    avram_p4_s3_original_negative_borel_cell_centred_L2_from_full_band
      X T n s t hst htT B hB hCut
  have hCE : P[(fun ω => H ω * ((N ω).toReal - r)) | 𝓕 s] =ᵐ[P] 0 :=
    avram_p4_f3_original_unbounded_predictable_negative_cell_condExp_auto
      X T n s t hst htT ε hε B hB hBand hCut H hH hHL2
  constructor
  · exact hHL2.integrable_mul hCountL2
  · calc
      ∫ ω, H ω * ((N ω).toReal - r) ∂P =
        ∫ ω, P[(fun ζ => H ζ * ((N ζ).toReal - r)) | 𝓕 s] ω ∂P :=
          (integral_condExp (𝓕.le s)).symm
      _ = ∫ ω, (0 : ℝ) ∂P := integral_congr_ae hCE
      _ = 0 := integral_zero Ω ℝ
