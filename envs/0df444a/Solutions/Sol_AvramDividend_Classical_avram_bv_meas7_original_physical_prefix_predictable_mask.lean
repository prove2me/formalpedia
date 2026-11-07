-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_meas7_original_physical_prefix_predictable_mask
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T08:54:38.634922+00:00
-- url     : https://prove2.me/submissions/bc76dac9-3b1b-46e5-b3e4-b1b88938df15

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_ruin_stopped_compact_previsible
import Mathlib.Data.NNReal.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The literal original controlled stopped pre-reserve mask at the
shrinking physical prefix is predictable in the right-continuous filtration. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ) (a b : ℕ → ℝ) :
    ∀ n : ℕ,
    let δ : ℕ → ℝ := fun k => T / ((k : ℝ) + 2)
    let S : ℝ≥0 := Real.toNNReal (T - δ n)
    let τ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (S : ℝ≥0∞)).toNNReal
    let E : Set (ℝ≥0 × Ω) := {p |
      (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc (a n) (b n)}
    (∀ ω, τ ω ≤ S) ∧
    IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)) ∧
    MeasurableSet[𝓕.rightCont.predictable] E ∧
    (∀ p ∈ E, Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc (a n) (b n)) ∧
    (∀ p ∈ E, p.1 ≤ S) := by
  intro n
  dsimp only
  exact avram_p3_g_localise_original_ruin_stopped_compact_previsible
    X x D hD (Real.toNNReal (T - T / ((n : ℝ) + 2))) (a n) (b n)
