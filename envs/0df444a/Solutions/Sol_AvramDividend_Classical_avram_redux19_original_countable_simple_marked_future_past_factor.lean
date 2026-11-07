-- Prove2me | solution 1 for AvramDividend.Classical.avram_redux19_original_countable_simple_marked_future_past_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:48:10.71706+00:00
-- url     : https://prove2.me/submissions/8a1bef7f-48a3-44ab-a986-67292a681816

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_countable_simple_marked_future_envelope
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_arbitrary_future_functional_past_weight_lintegral_factor
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-! Countable genuine original marked-jump future envelopes factor from the past. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s t : ℝ≥0) (hst : s ≤ t)
    (H : Ω → ℝ≥0∞) (hH : Measurable[𝓕 s] H)
    (n : ℕ → ℕ) (B : ∀ m, Fin (n m) → Set ℝ)
    (hB : ∀ m i, MeasurableSet (B m i))
    (w : ∀ m, Fin (n m) → ℝ≥0∞) :
    (∫⁻ ω, H ω * (⨆ m : ℕ, ∑ i : Fin (n m), w m i *
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ B m i)) ∂P) =
    (∫⁻ ω, H ω ∂P) *
      (∫⁻ ω, ⨆ m : ℕ, ∑ i : Fin (n m), w m i *
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B m i) ∂P) := by
  classical
  obtain ⟨Fpath, hF, hEq⟩ :=
    AvramDividend.Classical.avram_redux19_original_countable_simple_marked_future_envelope
      X s t hst n B hB w
  let G : Ω → ℝ≥0∞ := fun ω => ⨆ m : ℕ, ∑ i : Fin (n m), w m i *
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    (Ioc s t ×ˢ B m i)
  have hG : G = (fun ω => Fpath (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω)) := by
    funext ω
    exact hEq ω
  have hFactor :=
    AvramDividend.Classical.avram_wave7_01_original_arbitrary_future_functional_past_weight_lintegral_factor
      X s H hH Fpath hF
  change (∫⁻ ω, H ω * G ω ∂P) =
    (∫⁻ ω, H ω ∂P) * (∫⁻ ω, G ω ∂P)
  rw [hG]
  exact hFactor
