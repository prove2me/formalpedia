-- Prove2me | solution 1 for AvramDividend.Classical.avram_sweep16_20261106_admissible_initial_nonnegative_at_sample
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T06:34:50.454923+00:00
-- url     : https://prove2.me/submissions/26345d00-76c5-4117-83ca-bc6743bad7c9

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    ∀ ω : Ω, 0 ≤ x := by
  intro ω
  have hzero : D 0 ω = 0 := hD.1.1.1 ω
  have hmono : Monotone (fun t => D t ω) := hD.1.1.2.1 ω
  have hright : 0 ≤ rightLimit D 0 ω := by
    classical
    letI : Nonempty (Ioi (0 : ℝ≥0)) := ⟨⟨1, by norm_num⟩⟩
    unfold rightLimit
    apply le_ciInf
    intro s
    rw [← hzero]
    exact hmono (show (0 : ℝ≥0) ≤ (s : ℝ≥0) from zero_le)
  have hcap := hD.1.2 ω 0 (Or.inl rfl)
  dsimp [riskProcess] at hcap
  rw [hzero, X.X_zero ω] at hcap
  linarith
