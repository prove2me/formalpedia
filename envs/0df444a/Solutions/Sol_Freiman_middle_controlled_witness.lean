-- Prove2me | solution 1 for Freiman.middle_controlled_witness
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:04:08.24064+00:00
-- url     : https://prove2.me/submissions/f9229501-1388-4870-a842-05c02aac93eb

import Theorems.Thm_Freiman_middleRepair_initial_cover
import Theorems.Thm_Freiman_middleRepair_cover_realization
import Theorems.Thm_Freiman_middle_local_dominance
import Theorems.Thm_Freiman_middle_finite_exception_support
import Definitions.Def_Freiman_middleRepair

open Freiman

theorem solution :
    ∀ t ∈ Set.Icc (Real.sqrt 21) (128/25:ℝ), ∃ a : ℤ→ℕ+, localValue a 0=t ∧ (∀ i : ℤ, localValue a i ≤ t) ∧ (∃ N : ℕ, ∀ i : ℤ, N ≤ i.natAbs → (a i:ℕ) ≤ 3) := by
  intro t ht
  obtain ⟨r,hr,hg,hm⟩ := middleRepair_initial_cover t ht
  obtain ⟨a,ha,hat⟩ := middleRepair_cover_realization _ t hr hg hm
  exact ⟨a,hat,middle_local_dominance r a t ha hat ht.1,middle_finite_exception_support _ a ha⟩
