-- Prove2me | solution 1 for AvramDividend.Classical.chat03_martingale_monotone_clock_reindex
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T07:35:27.41528+00:00
-- url     : https://prove2.me/submissions/3b54415a-2202-4ae2-8eaf-3443c5e58197

import Mathlib

open MeasureTheory
open scoped NNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {G : Filtration ℝ≥0 mΩ}
    (M : ℝ≥0 → Ω → ℝ) (hM : Martingale M G P)
    (clock : ℕ → ℝ≥0) (hc : Monotone clock) :
    Martingale (fun k ω => M (clock k) ω)
      ({ seq := fun k => G (clock k),
         mono' := fun _ _ h => G.mono (hc h),
         le' := fun _ => G.le _ } : Filtration ℕ mΩ) P :=
  ⟨fun k => hM.1 (clock k), fun _ _ hij => hM.2 _ _ (hc hij)⟩
