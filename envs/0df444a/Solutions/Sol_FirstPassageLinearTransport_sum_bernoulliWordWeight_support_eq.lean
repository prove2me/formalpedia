-- Prove2me | solution 1 for FirstPassageLinearTransport.sum_bernoulliWordWeight_support_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:56:49.938702+00:00
-- url     : https://prove2.me/submissions/191a08b6-c7a5-466c-a762-edd0c8aae8dc

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Theorems.Thm_FirstPassageLinearTransport_bernoulliWordWeight_eq_support_card
import Theorems.Thm_FirstPassageLinearTransport_card_boolWords_support_eq
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
    (p : ℝ) (n k : ℕ) :
    ∑ v : Fin n → Bool,
        bernoulliWordWeight p v *
          (if (boolSupport v).card = k then 1 else 0) =
      tiltedBinomialMass p n k := by
  classical
  rw [show (∑ v : Fin n → Bool,
        bernoulliWordWeight p v *
          (if (boolSupport v).card = k then 1 else 0)) =
      ∑ v : Fin n → Bool,
        if (boolSupport v).card = k then
          p ^ k * (1 - p) ^ (n - k) else 0 by
    apply Finset.sum_congr rfl
    intro v _hv
    by_cases hcard : (boolSupport v).card = k
    · simp only [hcard, if_true, mul_one]
      rw [bernoulliWordWeight_eq_support_card, hcard]
    · simp [hcard]]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [card_boolWords_support_eq]
  unfold tiltedBinomialMass
  norm_cast
  ring
end FirstPassageLinearTransport
