-- Prove2me | solution 1 for AvramDividend.Classical.avram_gauss_ledger14_original_finite_cap_prepayment_V_eq_w
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T11:31:23.381746+00:00
-- url     : https://prove2.me/submissions/b6ac046a-1a3e-499c-84dd-7e84abe2a969

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_finite_realcap_invariant_all_times
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The capped admissible prepayment reserve never reaches the affine branch of V. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x c : ℝ) (hc : 0 ≤ c)
    (hxc : ENNReal.ofReal x ≤ ENNReal.ofReal c)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (w V : ℝ → ℝ)
    (hV : ∀ z : ℝ,
      V z = if z ≤ c then w z else w c + (z - c)) :
    ∀ (ω : Ω) (t : ℝ≥0),
      V (riskProcess X x D t ω) =
        w (riskProcess X x D t ω) := by
  intro ω t
  have hcap :=
    AvramDividend.Classical.avram_p4_e_localise_original_finite_realcap_invariant_all_times
      X x c hc hxc D hD ω t
  rw [hV]
  exact if_pos hcap
