-- Prove2me | solution 1 for CoffmanMitrani.H_subset_achievable
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-04T13:58:23.510593+00:00
-- url     : https://prove2.me/submissions/550e9328-e613-428a-b25a-d53e965260b5

import Mathlib
import Definitions.Def_CoffmanMitrani_H
import Definitions.Def_CoffmanMitrani_Achievable
import Theorems.Thm_CoffmanMitrani_theorem_1_mixing

/-! Reduction of `CoffmanMitrani.H_subset_achievable` (Coffman-Mitrani 1980, proof of Theorem 2,
p. 816: "Identifying the Sj's in Theorem 1 with the (achievable) preemptive priority disciplines")
to `CoffmanMitrani.theorem_1_mixing` (Theorem 1), reindexing `Fin D.M` as `Fin (K + 1)`. -/

open CoffmanMitrani in
theorem solution (D : Data) (W : Fin D.M → ℝ) (hW : W ∈ H D) :
    Achievable D W := by
  obtain ⟨π, Pv, α, hS, hα0, hα1, hWeq⟩ := hW
  choose S _hP hSS hA using hS
  obtain ⟨K, hK⟩ : ∃ K, D.M = K + 1 := ⟨D.M - 1, by have := D.one_le_M; omega⟩
  let e : Fin (K + 1) ≃ Fin D.M := finCongr hK.symm
  have hsum : ∑ j, α (e j) = 1 := by rw [Equiv.sum_comp e α]; exact hα1
  have hmix := theorem_1_mixing D (fun j => S (e j)) (fun j => Pv (e j)) (fun j => α (e j))
    (fun j => hSS (e j)) (fun j => hA (e j)) (fun j => hα0 (e j)) hsum
  refine ⟨_, hmix.1, ?_⟩
  have hW' : W = ∑ j, α (e j) • Pv (e j) := by
    rw [hWeq]; exact (Equiv.sum_comp e (fun m => α m • Pv m)).symm
  rw [hW']; exact hmix.2
