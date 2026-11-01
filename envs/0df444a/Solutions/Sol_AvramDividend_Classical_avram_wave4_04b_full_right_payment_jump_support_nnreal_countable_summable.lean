-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04b_full_right_payment_jump_support_nnreal_countable_summable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T13:27:10.899812+00:00
-- url     : https://prove2.me/submissions/c66c9a7d-bc78-4fca-bc27-d820ef40a0b3

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_full_right_payment_jump_support_summable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

noncomputable section

set_option maxHeartbeats 1000000 in
/-- Transport all actual finite-horizon chronological right-payment jumps
from the real Stieltjes time index to the original nonnegative filtration
time index used by the controlled Itô correction theorem. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) :
    let A : Set ℝ≥0 :=
      {t : ℝ≥0 | t ≤ T ∧ 0 < rightLimit D t ω - D t ω}
    A.Countable ∧
      Summable (fun t : A =>
        rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) := by
  dsimp only
  let B : Set ℝ :=
    {s : ℝ | 0 ≤ s ∧ s ≤ (T : ℝ) ∧
      0 < rightLimit D s.toNNReal ω - D s.toNNReal ω}
  let A : Set ℝ≥0 :=
    {t : ℝ≥0 | t ≤ T ∧ 0 < rightLimit D t ω - D t ω}
  have hReal :
      B.Countable ∧
        Summable (fun s : B =>
          rightLimit D ((s : ℝ).toNNReal) ω -
          D ((s : ℝ).toNNReal) ω) :=
    avram_wave4_04b_full_right_payment_jump_support_summable D hD ω T
  have hIn (t : A) : ((t : ℝ≥0) : ℝ) ∈ B := by
    have ht0 : (0 : ℝ) ≤ ((t : ℝ≥0) : ℝ) := (t : ℝ≥0).property
    have htT : ((t : ℝ≥0) : ℝ) ≤ (T : ℝ) := by
      exact_mod_cast t.property.1
    have htPos : 0 < rightLimit D (t : ℝ≥0) ω -
        D (t : ℝ≥0) ω := t.property.2
    change (0 : ℝ) ≤ ((t : ℝ≥0) : ℝ) ∧
      ((t : ℝ≥0) : ℝ) ≤ (T : ℝ) ∧
      0 < rightLimit D (((t : ℝ≥0) : ℝ).toNNReal) ω -
        D (((t : ℝ≥0) : ℝ).toNNReal) ω
    simpa only [Real.toNNReal_coe] using
      (show (0 : ℝ) ≤ ((t : ℝ≥0) : ℝ) ∧
        ((t : ℝ≥0) : ℝ) ≤ (T : ℝ) ∧
        0 < rightLimit D (t : ℝ≥0) ω -
          D (t : ℝ≥0) ω from ⟨ht0, htT, htPos⟩)
  let f : A → B := fun t => ⟨((t : ℝ≥0) : ℝ), hIn t⟩
  have hf : Function.Injective f := by
    intro t u h
    apply Subtype.ext
    apply NNReal.coe_injective
    exact congrArg (fun z : B => (z : ℝ)) h
  have hAeq : A = (fun t : ℝ≥0 => (t : ℝ)) ⁻¹' B := by
    ext t
    change (t ≤ T ∧ 0 < rightLimit D t ω - D t ω) ↔
      (0 : ℝ) ≤ (t : ℝ) ∧ (t : ℝ) ≤ (T : ℝ) ∧
        0 < rightLimit D ((t : ℝ).toNNReal) ω -
          D ((t : ℝ).toNNReal) ω
    simp only [Real.toNNReal_coe]
    constructor
    · rintro ⟨hT, hpos⟩
      refine ⟨t.property, ?_, hpos⟩
      exact_mod_cast hT
    · rintro ⟨_, hT, hpos⟩
      refine ⟨?_, hpos⟩
      exact_mod_cast hT
  have hAcount : A.Countable := by
    rw [hAeq]
    exact hReal.1.preimage NNReal.coe_injective
  have hAsum :
      Summable (fun t : A =>
        rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) := by
    have hc := hReal.2.comp_injective hf
    change Summable (fun t : A =>
      rightLimit D (((f t : B) : ℝ).toNNReal) ω -
        D (((f t : B) : ℝ).toNNReal) ω) at hc
    simpa only [f, Real.toNNReal_coe] using hc
  exact ⟨hAcount, hAsum⟩
