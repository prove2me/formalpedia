-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_ubv_original_nonmonotone_tailinf_stopping_localiser_package
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T17:51:50.323378+00:00
-- url     : https://prove2.me/submissions/ae4bdc21-fc1d-4314-adcf-34d89affb97b

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_ruin_clipped_tail_inf_stopping_times
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_ruin_min_liminf_clock_eq

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (S : ℕ → Ω → ℝ≥0∞)
    (hSstop : ∀ n, IsStoppingTime 𝓕.rightCont (S n))
    (hSliminfAE : ∀ᵐ ω ∂P,
      (⨆ n : ℕ, ⨅ k : ℕ, S (n + k) ω) = ⊤) :
    (∀ n : ℕ, IsStoppingTime 𝓕.rightCont
      (fun ω => ⨅ k : ℕ, min (ruinTime X x D ω) (S (n + k) ω))) ∧
    (∀ ω, Monotone
      (fun n : ℕ => ⨅ k : ℕ, min (ruinTime X x D ω) (S (n + k) ω))) ∧
    (∀ n ω, (⨅ k : ℕ, min (ruinTime X x D ω) (S (n + k) ω)) ≤
      ruinTime X x D ω) ∧
    (∀ᵐ ω ∂P,
      (⨆ n : ℕ, ⨅ k : ℕ, min (ruinTime X x D ω) (S (n + k) ω)) =
      ruinTime X x D ω) := by
  have hclock := avram_wave5_ubv_original_ruin_clipped_tail_inf_stopping_times
    X x C D hD S hSstop
  refine ⟨hclock.1, hclock.2.2, ?_, ?_⟩
  · intro n ω
    calc
      (⨅ k : ℕ, min (ruinTime X x D ω) (S (n + k) ω)) ≤
          min (ruinTime X x D ω) (S (n + 0) ω) :=
        iInf_le (fun k : ℕ => min (ruinTime X x D ω) (S (n + k) ω)) 0
      _ ≤ ruinTime X x D ω := min_le_left _ _
  · exact avram_wave5_ubv_original_ruin_min_liminf_clock_eq
      X x D S hSliminfAE
end
