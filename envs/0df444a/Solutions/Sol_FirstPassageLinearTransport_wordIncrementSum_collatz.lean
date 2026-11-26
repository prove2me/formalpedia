-- Prove2me | solution 1 for FirstPassageLinearTransport.wordIncrementSum_collatz
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:54:12.915272+00:00
-- url     : https://prove2.me/submissions/317e0137-5c3a-4c1b-b2b2-bc710ff8eed4

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Theorems.Thm_FirstPassageLinearTransport_collatzLogIncrement_eq
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
theorem _root_.solution
    {r : ℕ} (v : Fin r → Bool) :
    wordIncrementSum collatzLogIncrement v =
      ((boolSupport v).card : ℝ) * Real.log 3 - (r : ℝ) * Real.log 2 := by
  classical
  unfold wordIncrementSum
  simp_rw [collatzLogIncrement_eq]
  rw [Finset.sum_sub_distrib]
  rw [show (∑ i : Fin r, (if v i then Real.log 3 else 0)) =
      ∑ i ∈ (Finset.univ : Finset (Fin r)),
        (if v i = true then (1 : ℝ) else 0) * Real.log 3 by
    apply Finset.sum_congr rfl
    intro i _hi
    cases h : v i <;> simp [h]]
  rw [← Finset.sum_mul]
  simp [boolSupport]
end FirstPassageLinearTransport
