-- Prove2me | solution 1 for AvramDividend.Classical.avram_redux19_original_countable_simple_marked_future_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:37:44.387561+00:00
-- url     : https://prove2.me/submissions/2a7c0824-a506-4592-83b1-fbd2e7278afc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_finite_simple_marked_future_extractor
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-! An original marked future admits a measurable countable simple-mark envelope. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s t : ℝ≥0) (hst : s ≤ t)
    (n : ℕ → ℕ) (B : ∀ m, Fin (n m) → Set ℝ)
    (hB : ∀ m i, MeasurableSet (B m i))
    (w : ∀ m, Fin (n m) → ℝ≥0∞) :
    ∃ Fpath : (ℝ≥0 → ℝ) → ℝ≥0∞,
      Measurable Fpath ∧
      ∀ ω : Ω,
      (⨆ m : ℕ, ∑ i : Fin (n m), w m i *
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s t ×ˢ B m i)) =
        Fpath (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω) := by
  classical
  choose F hF hEq using (fun m : ℕ =>
    AvramDividend.Classical.avram_redux19_original_finite_simple_marked_future_extractor
      X s t hst (n m) (B m) (hB m) (w m))
  refine ⟨(fun Y => ⨆ m : ℕ, F m Y), ?_, ?_⟩
  · exact Measurable.iSup hF
  · intro ω
    change (⨆ m : ℕ, ∑ i : Fin (n m), w m i *
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B m i)) =
      ⨆ m : ℕ, F m (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω)
    apply iSup_congr
    intro m
    exact hEq m ω
