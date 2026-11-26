-- Prove2me | solution 1 for FirstPassageLinearTransport.affineCorrection_lt_two_pow_mul_three_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:38:24.768554+00:00
-- url     : https://prove2.me/submissions/189065c9-32fb-4d6c-b289-41be362f583c

import Definitions.Def_FirstPassageLinearTransport_MovingLowParameters
import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Definitions.Def_FirstPassageLinearTransport_TimeoutCore
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_lt_two
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_stageClock_zero
import Theorems.Thm_FirstPassageLinearTransport_stageOrbit_zero
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.bootstrapC_zero
attribute [local simp] FirstPassageLinearTransport.bootstrapD_zero
attribute [local simp] FirstPassageLinearTransport.bootstrapSet_zero
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.mem_taggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_transportedSources
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero
attribute [local simp] FirstPassageLinearTransport.stageClock_zero
attribute [local simp] FirstPassageLinearTransport.stageOrbit_zero



set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Topology
namespace FirstPassageLinearTransport
theorem _root_.solution (n k : ℕ) :
    affineCorrection n k < 2 ^ k * 3 ^ oddCount n k := by
  unfold affineCorrection
  have hsum :
      ∑ i ∈ Finset.range k,
          (parityBit n i : ℕ) * 2 ^ i *
            3 ^ (oddCount n k - oddCount n (i + 1))
        ≤ ∑ i ∈ Finset.range k, 2 ^ i * 3 ^ oddCount n k := by
    apply Finset.sum_le_sum
    intro i hi
    have hbit : (parityBit n i : ℕ) ≤ 1 := by
      have := parityBit_lt_two n i
      omega
    have hexp :
        3 ^ (oddCount n k - oddCount n (i + 1)) ≤
          3 ^ oddCount n k := by
      exact Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _)
    calc
      (parityBit n i : ℕ) * 2 ^ i *
            3 ^ (oddCount n k - oddCount n (i + 1))
          ≤ 1 * 2 ^ i *
            3 ^ (oddCount n k - oddCount n (i + 1)) := by
              exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hbit)
      _ ≤ 2 ^ i * 3 ^ oddCount n k := by
        simpa using Nat.mul_le_mul_left (2 ^ i) hexp
  calc
    ∑ i ∈ Finset.range k,
        (parityBit n i : ℕ) * 2 ^ i *
          3 ^ (oddCount n k - oddCount n (i + 1))
        ≤ ∑ i ∈ Finset.range k, 2 ^ i * 3 ^ oddCount n k := hsum
    _ = (∑ i ∈ Finset.range k, 2 ^ i) * 3 ^ oddCount n k := by
      rw [Finset.sum_mul]
    _ = (2 ^ k - 1) * 3 ^ oddCount n k := by
      rw [Nat.geomSum_eq (by omega : 2 ≤ 2)]
      norm_num
    _ < 2 ^ k * 3 ^ oddCount n k := by
      have hpow : 0 < 3 ^ oddCount n k := pow_pos (by omega) _
      have htwo : 0 < 2 ^ k := pow_pos (by omega) _
      exact Nat.mul_lt_mul_of_pos_right (by omega) hpow
end FirstPassageLinearTransport
