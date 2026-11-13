-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a27_continuous_last_increment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T08:51:25.759738+00:00
-- url     : https://prove2.me/submissions/18a2831c-3933-4624-8520-080e74984d70

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter
open scoped NNReal
noncomputable section

theorem solution
    (f : ℝ≥0 → ℝ) (s : Set ℝ≥0) (t : ℝ≥0) (u : ℕ → ℝ≥0)
    (hf : ContinuousWithinAt f s t)
    (hu : Tendsto u atTop (nhds t))
    (hmem : ∀ᶠ m in atTop, u m ∈ s) :
    Tendsto (fun m => f t - f (u m)) atTop (nhds (0 : ℝ)) := by
  have hwithin : Tendsto u atTop (nhdsWithin t s) :=
    tendsto_nhdsWithin_iff.mpr ⟨hu, hmem⟩
  have hfun : Tendsto (fun m => f (u m)) atTop (nhds (f t)) :=
    hf.tendsto.comp hwithin
  have hconst : Tendsto (fun _ : ℕ => f t) atTop (nhds (f t)) :=
    tendsto_const_nhds
  convert hconst.sub hfun using 1 <;> simp
