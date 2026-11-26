-- Prove2me | solution 1 for FirstPassageLinearTransport.periodicMultiplicativeHitBlock_crosses
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:33:32.50801+00:00
-- url     : https://prove2.me/submissions/c03360e4-d90b-4511-af57-d14196d016bb

import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_ReciprocalHeightObstruction
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_cons
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_scale
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_zero
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_boolParityWord_mod
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_card_boolSupport_cons
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_stageClock_zero
import Theorems.Thm_FirstPassageLinearTransport_stageOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_stoppedBallotValue_cons
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_cons
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_scale
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_zero
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.bootstrapC_zero
attribute [local simp] FirstPassageLinearTransport.bootstrapD_zero
attribute [local simp] FirstPassageLinearTransport.bootstrapSet_zero
attribute [local simp] FirstPassageLinearTransport.card_boolSupport_cons
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.mem_taggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_transportedSources
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.rawOrbit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero
attribute [local simp] FirstPassageLinearTransport.stageClock_zero
attribute [local simp] FirstPassageLinearTransport.stageOrbit_zero
attribute [local simp] FirstPassageLinearTransport.stoppedBallotValue_cons



set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {N t h n : ℕ} {u : ℝ}
    (hn : n ∈ periodicMultiplicativeHitBlock N t h u) :
    N ≤ n ∧ n < t * 2 ^ h ∧
      crossesMultiplicativeFrom u h 1 (boolParityWord h n) := by
  classical
  rw [periodicMultiplicativeHitBlock, Finset.mem_map] at hn
  obtain ⟨p, hp, rfl⟩ := hn
  have hpMem := Finset.mem_product.mp hp
  have hpBlock := Finset.mem_Ico.mp hpMem.1
  have hpResidue := hpMem.2
  have hqPos : 0 < 2 ^ h := pow_pos (by omega) h
  have hlower : N ≤ (Nat.divModEquiv (2 ^ h)).symm p := by
    rw [Nat.divModEquiv_symm_apply]
    have hqOne : 1 ≤ 2 ^ h := hqPos
    calc
      N ≤ p.1 := hpBlock.1
      _ = p.1 * 1 := by omega
      _ ≤ p.1 * 2 ^ h := Nat.mul_le_mul_left p.1 hqOne
      _ ≤ p.1 * 2 ^ h + p.2 := Nat.le_add_right _ _
  have hupper : (Nat.divModEquiv (2 ^ h)).symm p < t * 2 ^ h := by
    rw [Nat.divModEquiv_symm_apply]
    calc
      p.1 * 2 ^ h + p.2 < p.1 * 2 ^ h + 2 ^ h :=
        Nat.add_lt_add_left p.2.isLt _
      _ = (p.1 + 1) * 2 ^ h := by ring
      _ ≤ t * 2 ^ h :=
        Nat.mul_le_mul_right (2 ^ h) (Nat.succ_le_of_lt hpBlock.2)
  have hcrossCode :
      crossesMultiplicativeFrom u h 1 (boolParityCode h p.2) := by
    rw [multiplicativeHitResidues] at hpResidue
    exact (Finset.mem_filter.mp hpResidue).2
  have hmod :
      (Nat.divModEquiv (2 ^ h)).symm p % 2 ^ h = p.2 := by
    rw [Nat.divModEquiv_symm_apply]
    simp [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt p.2.isLt]
  have hword :
      boolParityCode h p.2 =
        boolParityWord h ((Nat.divModEquiv (2 ^ h)).symm p) := by
    rw [boolParityCode_eq_word]
    change boolParityWord h (p.2 : ℕ) =
      boolParityWord h ((Nat.divModEquiv (2 ^ h)).symm p)
    rw [← hmod, boolParityWord_mod]
  refine ⟨hlower, hupper, ?_⟩
  change crossesMultiplicativeFrom u h 1
    (boolParityWord h ((Nat.divModEquiv (2 ^ h)).symm p))
  rwa [← hword]
end FirstPassageLinearTransport
