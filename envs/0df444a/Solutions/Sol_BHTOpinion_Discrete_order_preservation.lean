-- Prove2me | solution 1 for BHTOpinion.Discrete.order_preservation
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:19:34.08419+00:00
-- url     : https://prove2.me/submissions/43fc018a-4473-41c4-8753-1a137200acd9

import Mathlib
import Definitions.Def_BHTOpinion_Discrete_Model

open Filter Topology

open BHTOpinion.Discrete in
theorem solution {n : ℕ} (x : ℝ → Fin n → ℝ) (hx : IsProperSolution x)
    (i j : Fin n) (t t' : ℝ) (ht : 0 ≤ t) (htt' : t ≤ t') (hij : x t j ≤ x t i) :
    x t' j ≤ x t' i := by
  by_contra hlt
  push_neg at hlt
  have hxc : ContinuousOn x (Set.Ici 0) := hx.1.1
  have hc : ContinuousOn (fun s => x s i - x s j) (Set.Icc t t') := by
    have h1 := ((continuous_apply i).comp_continuousOn hxc).sub
      ((continuous_apply j).comp_continuousOn hxc)
    exact h1.mono (fun s hs => le_trans ht hs.1)
  have hmem : (0 : ℝ) ∈ Set.Icc (x t' i - x t' j) (x t i - x t j) :=
    ⟨by linarith, by linarith⟩
  obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc' htt' hc hmem
  have heq : x s i = x s j := by simp only at hs0; linarith
  have := hx.2.2.2 i j s (le_trans ht hs.1) heq t' hs.2
  linarith
