-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_finitecap_admissible_upperstrip_expected_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T17:23:50.972405+00:00
-- url     : https://prove2.me/submissions/a675821d-1962-45a7-bfbb-89e97b13dc1e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_admissibleLe_riskProcess_le_cap_all_times
import Theorems.Thm_AvramDividend_Classical_avram_gfinite64_original_global_cap_strip_expected_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) :
    Tendsto
      (fun j : ℕ => ∫ ω, ∫ t in Ioo (0 : ℝ) (n : ℝ),
        if C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ)) <
            riskProcess X x D (Real.toNNReal t) ω
        then (1 : ℝ) else 0 ∂volume ∂P)
      atTop (𝓝 (0 : ℝ)) := by
  have hCapPos : 0 < C.toReal :=
    ENNReal.toReal_pos (ne_of_gt hC) hFinite
  have hCap : ∀ ω (s : ℝ≥0), riskProcess X x D s ω ≤ C.toReal := by
    intro ω t
    have hLe := admissibleLe_riskProcess_le_cap_all_times
      X x C D hD hxc ω t
    exact (ENNReal.ofReal_le_iff_le_toReal hFinite).mp hLe
  exact avram_gfinite64_original_global_cap_strip_expected_zero
    X hBV x C.toReal hCapPos D hD.1.1 hCap n hn
