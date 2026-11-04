-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_finite_cap_stopped_terminal_reserve_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:00:39.162473+00:00
-- url     : https://prove2.me/submissions/bc0884ea-4543-4b05-beac-934f7561b4a7

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_finite_realcap_invariant_all_times
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- On the source probability space, the true stopped postpayment-or-ruin
    terminal reserve never exceeds the finite admissibility cap. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x c : ℝ) (hc : 0 ≤ c)
    (hxc : ENNReal.ofReal x ≤ ENNReal.ofReal c)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (τ : Ω → ℝ≥0) (W : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω) :
    ∀ ω, W ω ≤ c := by
  intro ω
  have hCap :=
    avram_p4_e_localise_original_finite_realcap_invariant_all_times
      X x c hc hxc D hD ω (τ ω)
  rw [hW ω]
  split_ifs with hpre
  · have hDiv : D (τ ω) ω ≤ rightLimit D (τ ω) ω :=
      dividendStrategy_le_rightLimit D hD.1.1 ω (τ ω)
    dsimp [riskProcess] at hCap
    linarith
  · exact hCap
