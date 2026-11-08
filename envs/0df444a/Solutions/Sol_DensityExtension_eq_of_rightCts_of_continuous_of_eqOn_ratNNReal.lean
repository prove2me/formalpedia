-- Prove2me | solution 1 for DensityExtension.eq_of_rightCts_of_continuous_of_eqOn_ratNNReal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T17:21:26.774378+00:00
-- url     : https://prove2.me/submissions/b3808e68-2d42-4a8a-9e97-1670db096a89

import Mathlib.Data.NNReal.Defs
import Mathlib.Topology.Separation.Hausdorff
import Definitions.Def_LeanLevy_Levy_CharacteristicExponent
import Theorems.Thm_levy_foundations_eq_of_rightCts_of_continuous_of_eqOn_ratNNReal

open Filter Topology
open scoped NNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution {β : Type*} [TopologicalSpace β] [T2Space β]
    {f g : ℝ≥0 → β}
    (hf : ∀ t, ContinuousWithinAt f (Set.Ici t) t)
    (hg : Continuous g)
    (heq : ∀ (k n : ℕ),
      f ((k : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0)) =
      g ((k : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0))) :
    f = g := by
  exact levy_foundations_eq_of_rightCts_of_continuous_of_eqOn_ratNNReal hf hg heq
