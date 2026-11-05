-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_e_compensator_original_levy_negative_mark_sigmaFinite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:53:22.520228+00:00
-- url     : https://prove2.me/submissions/ae0dfa67-62cb-40c2-8f42-a875b48d24f2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_negative_levy_mark_tail_finite_mass_at_every_small_threshold
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_sigma_finite_of_negative_tail_cover
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The exact original Lévy triplet measure is sigma-finite. -/
theorem solution
{Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
{𝓕 : Filtration ℝ≥0 mΩ}
(X : SpectrallyNegativeLevy P 𝓕) :
SigmaFinite X.ν := by
  have hfin : ∀ ε : ℝ, 0 < ε → X.ν (Iic (-ε)) < ⊤ := by
    intro ε hε
    let δ : ℝ := min ε 1
    have hδ0 : 0 < δ := lt_min hε zero_lt_one
    have hδ1 : δ ≤ 1 := min_le_right _ _
    have hδle : δ ≤ ε := min_le_left _ _
    have htail : X.ν (Iic (-δ)) < ⊤ :=
      avram_wave7_02_original_negative_levy_mark_tail_finite_mass_at_every_small_threshold
        X.ν X.ν_integrable δ hδ0 hδ1
    have hsubset : Iic (-ε) ⊆ Iic (-δ) := by
      intro z hz
      exact le_trans hz (neg_le_neg hδle)
    exact lt_of_le_of_lt (measure_mono hsubset) htail
  exact avram_p2_c_borel_sigma_finite_of_negative_tail_cover
    X.ν X.ν_Ici hfin
