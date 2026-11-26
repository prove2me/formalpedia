-- Prove2me | solution 1 for FirstPassageLinearTransport.tiltedBinomialMass_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:53:42.281218+00:00
-- url     : https://prove2.me/submissions/1028169f-e1f7-4730-abf0-a63e38016ee0

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Theorems.Thm_FirstPassageLinearTransport_tiltedBinomialMass_nonneg
import Theorems.Thm_FirstPassageLinearTransport_sum_tiltedBinomialMass
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
    {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (n k : ℕ) :
    tiltedBinomialMass p n k ≤ 1 := by
  by_cases hkn : k ≤ n
  · have hmem : k ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
    have hle : tiltedBinomialMass p n k ≤
        ∑ j ∈ Finset.range (n + 1), tiltedBinomialMass p n j := by
      exact Finset.single_le_sum
        (fun j _ => tiltedBinomialMass_nonneg hp₀ hp₁ n j) hmem
    simpa [sum_tiltedBinomialMass n] using hle
  · have hnk : n < k := Nat.lt_of_not_ge hkn
    simp [tiltedBinomialMass, Nat.choose_eq_zero_of_lt hnk]
end FirstPassageLinearTransport
