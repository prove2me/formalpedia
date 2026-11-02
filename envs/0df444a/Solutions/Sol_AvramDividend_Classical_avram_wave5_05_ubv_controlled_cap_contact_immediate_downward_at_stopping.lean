-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_05_ubv_controlled_cap_contact_immediate_downward_at_stopping
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:08:31.904746+00:00
-- url     : https://prove2.me/submissions/be09dc81-9db5-4fa6-89a6-85aeae099236

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_ubv_original_levy_finite_stopping_downward_regular_no_grid

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-!
The controlled reserve of the original UBV source immediately enters below
its current value after every finite stopping time, including time zero.
Nondecreasing same-filtration dividend payments only reinforce the decrease.
-/

/-- Source-faithful controlled downcrossing across every cap contact. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x c : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω : Ω | τ ω ≤ s})
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0))) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ s : ℝ≥0, 0 < s ∧ s < ε ∧
        riskProcess X x D (τ ω + s) ω < riskProcess X x D (τ ω) ω ∧
        (riskProcess X x D (τ ω) ω ≤ c →
          riskProcess X x D (τ ω + s) ω < c) := by
  have hDown :=
    avram_wave4_04_ubv_original_levy_finite_stopping_downward_regular_no_grid
      X hBV τ hτ hstop
  filter_upwards [hDown] with ω hω
  intro ε hε
  obtain ⟨s, hslt, hsNeg⟩ := hω ε hε
  have hspos : 0 < s := by
    by_contra hnot
    have hs0 : s = 0 :=
      le_antisymm (le_of_not_gt hnot) (zero_le : (0 : ℝ≥0) ≤ s)
    subst s
    simp at hsNeg
  have hDmono : Monotone (fun t : ℝ≥0 => D t ω) := hD.2.1 ω
  have hDle : D (τ ω) ω ≤ D (τ ω + s) ω :=
    hDmono (le_add_of_nonneg_right (zero_le : (0 : ℝ≥0) ≤ s))
  have hDecrease : riskProcess X x D (τ ω + s) ω <
      riskProcess X x D (τ ω) ω := by
    dsimp [riskProcess]
    linarith
  exact ⟨s, hspos, hslt, hDecrease,
    fun hcap => lt_of_lt_of_le hDecrease hcap⟩
