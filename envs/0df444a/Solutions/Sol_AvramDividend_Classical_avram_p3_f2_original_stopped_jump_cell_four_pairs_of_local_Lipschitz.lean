-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_f2_original_stopped_jump_cell_four_pairs_of_local_Lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T18:32:54.332343+00:00
-- url     : https://prove2.me/submissions/1dcf060c-e9b9-4930-8ce7-463f137e3af7

import Mathlib
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section


theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (K : ℝ) (U : Set ℝ)
    (ω : Ω) (u : ℕ → ℝ≥0) (n : ℕ) :
    let J : ℝ≥0 → ℝ := fun t =>
      ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
        Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
    let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
    let z : ℕ → ℝ := fun i =>
      x + X.X (u i) ω - rightLimit D (u i) ω
    let c : ℕ → ℝ := fun i => Y (u (i + 1)) - Y (u i)
    let j : ℕ → ℝ := fun i => J (u (i + 1)) - J (u i)
    (∀ i, i < n → z i ∈ U ∧ z i + c i ∈ U ∧
      z i - j i ∈ U ∧ z i + c i - j i ∈ U) →
    (∀ a ∈ U, ∀ b ∈ U, |w a - w b| ≤ K * |a - b|) →
    ∀ i, i < n →
      (|w (z i + c i - j i) - w (z i - j i)| ≤ K * |c i|) ∧
      (|w (z i + c i) - w (z i)| ≤ K * |c i|) ∧
      (|w (z i + c i - j i) - w (z i + c i)| ≤ K * |j i|) ∧
      (|w (z i - j i) - w (z i)| ≤ K * |j i|) := by
  intro J Y z c j hPts hLip i hi
  rcases hPts i hi with ⟨hz, hzc, hzj, hzcj⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only
      [show (z i + c i - j i) - (z i - j i) = c i by ring]
      using (hLip (z i + c i - j i) hzcj (z i - j i) hzj)
  · simpa only
      [show (z i + c i) - z i = c i by ring]
      using (hLip (z i + c i) hzc (z i) hz)
  · simpa only
      [show (z i + c i - j i) - (z i + c i) = -(j i) by ring, abs_neg]
      using (hLip (z i + c i - j i) hzcj (z i + c i) hzc)
  · simpa only
      [show (z i - j i) - z i = -(j i) by ring, abs_neg]
      using (hLip (z i - j i) hzj (z i) hz)
