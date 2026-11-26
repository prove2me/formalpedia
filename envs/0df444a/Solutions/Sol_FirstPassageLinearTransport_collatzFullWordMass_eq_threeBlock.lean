-- Prove2me | solution 1 for FirstPassageLinearTransport.collatzFullWordMass_eq_threeBlock
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:56:48.048458+00:00
-- url     : https://prove2.me/submissions/d1b77a18-d87d-4fb2-a723-31e509d0e657

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Theorems.Thm_FirstPassageLinearTransport_bernoulliWordWeight_rev
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
    (p : ℝ) (a b : ℕ) (B q : ℝ) :
    collatzFullWordMass p (a + (b + a)) B q =
      collatzFullThreeBlockMass p a b B q := by
  classical
  unfold collatzFullWordMass collatzFullThreeBlockMass
  rw [← (collatzThreeBlockSummationEquiv a b).sum_comp]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro u _hu
  apply Finset.sum_congr rfl
  intro w _hw
  apply Finset.sum_congr rfl
  intro v _hv
  rw [collatzThreeBlockSummationEquiv_apply]
  simp only [collatzThreeBlockWord, bernoulliWordWeight_append,
    bernoulliWordWeight_rev]
  ring
end FirstPassageLinearTransport
