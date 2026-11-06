-- Prove2me | solution 1 for BianchiIX.unique_crossing_of_opposite_monotonicity
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T07:03:27.690256+00:00
-- url     : https://prove2.me/submissions/49471e1c-c7db-4c15-b07b-12ed8712de9c

import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set


theorem solution {V W : ℝ → ℝ} {s t : ℝ}
    (hst : s < t) (hV : ContinuousOn V (Icc s t)) (hW : ContinuousOn W (Icc s t))
    (hVa : StrictAntiOn V (Icc s t)) (hWm : StrictMonoOn W (Icc s t))
    (hs : W s < V s) (ht : V t < W t) : ∃! r, r ∈ Ioo s t ∧ V r = W r := by
  let f := fun r => W r - V r
  have hf : ContinuousOn f (Icc s t) := hW.sub hV
  have hmono : StrictMonoOn f (Icc s t) := by
    intro a ha b hb hab
    have H := hVa ha hb hab
    have H' := hWm ha hb hab
    dsimp [f]
    linarith only [H, H']
  obtain ⟨r, hr, hzero⟩ := intermediate_value_Icc hst.le hf
    (show (0 : ℝ) ∈ Icc (f s) (f t) by constructor <;> dsimp [f] <;> linarith only [hs, ht])
  have hsr : s < r := lt_of_le_of_ne hr.1 (by
    intro heq
    subst r
    dsimp [f] at hzero
    linarith only [hzero, hs])
  have hrt : r < t := lt_of_le_of_ne hr.2 (by
    intro heq
    subst r
    dsimp [f] at hzero
    linarith only [hzero, ht])
  refine ⟨r, ⟨⟨hsr, hrt⟩, ?_⟩, ?_⟩
  · dsimp [f] at hzero
    linarith only [hzero]
  · intro u hu
    apply hmono.injOn (Ioo_subset_Icc_self hu.1) hr
    change W u - V u = f r
    rw [hzero, hu.2, sub_self]
