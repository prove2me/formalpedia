-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_cstar_deriv_pos_of_root_smooth
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T00:03:12.375394+00:00
-- url     : https://prove2.me/submissions/c575b482-1e54-4dd6-a9a0-b89960a0b9cf

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_scaleDeriv_pos_of_gaussian_or_bv
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_cstar_nonzero_of_vcstar_C2
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_nonneg

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Every root smoothness branch yields a positive local scale slope at cstar. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioi (0 : ℝ))) :
    0 < deriv W (cstar W).toReal := by
  have ha : 0 < (cstar W).toReal :=
    (ENNReal.toReal_pos_iff).mpr ⟨hcpos, hc⟩
  rcases h_smooth with hσ | hBV | hC2
  · exact avram_wave3_02_scaleDeriv_pos_of_gaussian_or_bv
      X hX q hq W hW (Or.inl hσ) _ ha
  · exact avram_wave3_02_scaleDeriv_pos_of_gaussian_or_bv
      X hX q hq W hW (Or.inr hBV) _ ha
  · have hnonneg := scaleDeriv_nonneg X q W hW _ ha
    have hne := avram_wave3_02_cstar_nonzero_of_vcstar_C2 W hc hcpos hC2
    exact lt_of_le_of_ne hnonneg (Ne.symm hne)
