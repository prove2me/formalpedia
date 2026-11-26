-- Prove2me | solution 1 for FirstPassageLinearTransport.sum_tiltedBinomialMass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:52:51.818903+00:00
-- url     : https://prove2.me/submissions/fba96109-9fef-43ec-9bb9-33d531b3148e

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
theorem _root_.solution
    {p : ℝ} (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), tiltedBinomialMass p n k = 1 := by
  calc
    ∑ k ∈ Finset.range (n + 1), tiltedBinomialMass p n k =
        ∑ k ∈ Finset.range (n + 1),
          p ^ k * (1 - p) ^ (n - k) * (n.choose k : ℝ) := by
      apply Finset.sum_congr rfl
      intro k hk
      unfold tiltedBinomialMass
      ring
    _ = (p + (1 - p)) ^ n := (add_pow p (1 - p) n).symm
    _ = 1 := by simp
end FirstPassageLinearTransport
