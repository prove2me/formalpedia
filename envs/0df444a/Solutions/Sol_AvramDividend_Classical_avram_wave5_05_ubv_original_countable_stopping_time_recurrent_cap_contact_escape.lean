-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_05_ubv_original_countable_stopping_time_recurrent_cap_contact_escape
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T12:25:26.415203+00:00
-- url     : https://prove2.me/submissions/807a9a5f-bfde-4ce9-81b8-189b34c28cab

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_surviving_cap_stopping_enters_strict_subcap_immediately

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-!
The true UBV source reserve cannot remain pinned at the cap after
any of countably many stopping-time contacts, simultaneously on a
single P-full event. This permits restarted cap-contact localisation
including the deterministic time-zero stopping time.
-/

/-- Strictly subcap points follow countably many cap-contact stopping times. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x c : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (τ : ℕ → Ω → ℝ≥0)
    (hτ : ∀ n, ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] {ω : Ω | τ n ω ≤ s})
    (hStop : ∀ n, IsStoppingTime 𝓕
      (fun ω : Ω => (τ n ω : WithTop ℝ≥0))) :
    ∀ᵐ ω ∂P, ∀ n : ℕ,
      (τ n ω : ℝ≥0∞) < ruinTime X x D ω →
      riskProcess X x D (τ n ω) ω = c →
      ∀ ε : ℝ≥0, 0 < ε →
        ∃ s : ℝ≥0, τ n ω < s ∧ s < τ n ω + ε ∧
          (s : ℝ≥0∞) < ruinTime X x D ω ∧
          riskProcess X x D s ω < c := by
  apply (ae_all_iff).2
  intro n
  have hBase :=
    avram_wave5_05_ubv_original_surviving_cap_stopping_enters_strict_subcap_immediately
      X hBV x c D hD (τ n) (hτ n) (hStop n)
  filter_upwards [hBase] with ω hω
  intro hSurvive hCapContact ε hε
  obtain ⟨s, hs0, hsε, hsSurvive, hsBelow⟩ :=
    hω hSurvive hCapContact ε hε
  refine ⟨τ n ω + s, ?_, ?_, hsSurvive, hsBelow⟩
  · simpa using add_lt_add_left hs0 (τ n ω)
  · simpa [add_comm] using add_lt_add_left hsε (τ n ω)
