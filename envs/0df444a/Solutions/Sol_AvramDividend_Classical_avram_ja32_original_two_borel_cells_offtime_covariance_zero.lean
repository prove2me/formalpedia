-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja32_original_two_borel_cells_offtime_covariance_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T18:58:22.329327+00:00
-- url     : https://prove2.me/submissions/dc6568ca-9eb7-49d9-bcb0-07627f6f0217

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja29_original_negative_borel_cell_centred_L2_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ja31_original_borel_mark_count_filtration_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_unbounded_predictable_cell_L1_integral_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Arbitrary original Borel past and future marked cells have zero
cross covariance by physical adaptedness and predictable compensation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (cutp : ℕ) (Bp : Set ℝ) (hBp : MeasurableSet Bp)
    (hSepP : Bp ⊆ Iic (-(1 / ((cutp : ℝ) + 1))))
    (cutf : ℕ) (ε : ℝ) (hε : 0 < ε)
    (Bf : Set ℝ) (hBf : MeasurableSet Bf)
    (hBandF : Bf ⊆ Ioo (-1 : ℝ) (-ε))
    (hCutF : Bf ⊆ Iic (-(1 / ((cutf : ℝ) + 1)))) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let A : Ω → ℝ≥0∞ := fun ω => NX ω (Ioc 0 s ×ˢ Bp)
    let F : Ω → ℝ≥0∞ := fun ω => NX ω (Ioc s t ×ˢ Bf)
    let rp : ℝ := ((s : ℝ≥0∞) * X.ν Bp).toReal
    let rf : ℝ := (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν Bf).toReal
    Integrable (fun ω => ((A ω).toReal - rp) * ((F ω).toReal - rf)) P ∧
    (∫ ω, ((A ω).toReal - rp) * ((F ω).toReal - rf) ∂P) = 0 := by
  letI : IsProbabilityMeasure P := X.isProbability
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let A : Ω → ℝ≥0∞ := fun ω => NX ω (Ioc 0 s ×ˢ Bp)
  let F : Ω → ℝ≥0∞ := fun ω => NX ω (Ioc s t ×ˢ Bf)
  let rp : ℝ := ((s : ℝ≥0∞) * X.ν Bp).toReal
  let rf : ℝ := (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν Bf).toReal
  let H : Ω → ℝ := fun ω => (A ω).toReal - rp
  change Integrable (fun ω => H ω * ((F ω).toReal - rf)) P ∧
    (∫ ω, H ω * ((F ω).toReal - rf) ∂P) = 0
  have hAm : Measurable[𝓕 s] A := by
    exact avram_ja31_original_borel_mark_count_filtration_measurable
      X s Bp hBp
  have hHm : Measurable[𝓕 s] H :=
    (ENNReal.measurable_toReal.comp hAm).sub_const rp
  have hHs : StronglyMeasurable[𝓕 s] H := hHm.stronglyMeasurable
  have hSq : Integrable (fun ω => (H ω) ^ 2) P := by
    have h := avram_ja29_original_negative_borel_cell_centred_L2_integrable
      X s cutp Bp hBp hSepP
    exact h.2.2
  have hL2 : MemLp H 2 P :=
    (memLp_two_iff_integrable_sq
      ((hHm.mono (𝓕.le s) le_rfl).aestronglyMeasurable)).2 hSq
  have hSource :=
    avram_p4_f3_original_unbounded_predictable_cell_L1_integral_zero
      X t cutf s t hst le_rfl ε hε Bf hBf hBandF hCutF
      H hHs hL2
  change Integrable (fun ω => H ω * ((F ω).toReal - rf)) P ∧
    (∫ ω, H ω * ((F ω).toReal - rf) ∂P) = 0 at hSource
  exact hSource
