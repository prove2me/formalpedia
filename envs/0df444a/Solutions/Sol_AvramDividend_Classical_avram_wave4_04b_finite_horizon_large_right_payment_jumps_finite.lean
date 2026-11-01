-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04b_finite_horizon_large_right_payment_jumps_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T13:38:52.31319+00:00
-- url     : https://prove2.me/submissions/79216091-74aa-4ba2-b4ff-261ff7edd32c

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_full_right_payment_jump_support_summable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

noncomputable section

set_option maxHeartbeats 1000000 in
/-- All actual chronological right-dividend jumps above any fixed positive
size threshold form a finite set in a finite window. This excludes Zeno
accumulation of macroscopic atoms but permits diffuse dividend mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) :
    let A : Set ℝ :=
      {s : ℝ | 0 ≤ s ∧ s ≤ (T : ℝ) ∧
        0 < rightLimit D s.toNNReal ω - D s.toNNReal ω}
    ∀ ε : ℝ, 0 < ε →
      {s : A | ε ≤ rightLimit D ((s : ℝ).toNNReal) ω -
        D ((s : ℝ).toNNReal) ω}.Finite := by
  dsimp only
  let A : Set ℝ :=
    {s : ℝ | 0 ≤ s ∧ s ≤ (T : ℝ) ∧
      0 < rightLimit D s.toNNReal ω - D s.toNNReal ω}
  let δ : A → ℝ := fun s =>
    rightLimit D ((s : ℝ).toNNReal) ω -
      D ((s : ℝ).toNNReal) ω
  have hSupport :
      A.Countable ∧ Summable δ :=
    avram_wave4_04b_full_right_payment_jump_support_summable D hD ω T
  intro ε hε
  have hTendsto :
      Filter.Tendsto δ Filter.cofinite (𝓝 (0 : ℝ)) :=
    hSupport.2.tendsto_cofinite_zero
  have hNear : Iio ε ∈ 𝓝 (0 : ℝ) :=
    isOpen_Iio.mem_nhds hε
  have hEvent : δ ⁻¹' Iio ε ∈ Filter.cofinite :=
    hTendsto hNear
  have hFinite : ((δ ⁻¹' Iio ε)ᶜ).Finite :=
    Filter.mem_cofinite.mp hEvent
  change {s : A | ¬ δ s < ε}.Finite at hFinite
  simpa only [not_lt, δ] using hFinite
