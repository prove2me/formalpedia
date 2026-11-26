-- Prove2me | solution 1 for FirstPassageLinearTransport.exists_tiltedBinomialMass_maximizer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:53:20.83093+00:00
-- url     : https://prove2.me/submissions/0c515461-6295-47b6-9393-0216914f5b04

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero



set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution (p : ℝ) (n : ℕ) :
    ∃ k₀ : ℕ, k₀ ≤ n ∧ ∀ k : ℕ, k ≤ n →
      tiltedBinomialMass p n k ≤ tiltedBinomialMass p n k₀ := by
  have hne : (Finset.range (n + 1)).Nonempty := ⟨0, by simp⟩
  obtain ⟨k₀, hk₀, hmax⟩ :=
    Finset.exists_max_image (Finset.range (n + 1))
      (tiltedBinomialMass p n) hne
  have hk₀le : k₀ ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk₀)
  refine ⟨k₀, hk₀le, ?_⟩
  intro k hk
  exact hmax k (Finset.mem_range.mpr (by omega))
end FirstPassageLinearTransport
