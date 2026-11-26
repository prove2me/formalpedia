-- Prove2me | solution 1 for FirstPassageLinearTransport.badCount_le_shell_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:22:07.930198+00:00
-- url     : https://prove2.me/submissions/4436e350-60a3-4d02-b6dd-093e7cb663c2

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_FirstPassageLinearTransport_Basic
import Definitions.Def_FirstPassageLinearTransport_Density
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_badCount_subset_biUnion
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero


attribute [local simp] FirstPassageLinearTransport.mem_prefixBad

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution (S : Set ℕ) (X : ℕ) :
    badCount S X ≤
      ∑ M ∈ Finset.range (Nat.log 2 X + 1), (shellBad S M).card := by
  classical
  unfold badCount
  calc
    ((Finset.Icc 1 X).filter fun n => n ∉ S).card ≤
        ((Finset.range (Nat.log 2 X + 1)).biUnion (shellBad S)).card :=
      Finset.card_le_card (by
        simpa [prefixBad] using badCount_subset_biUnion S X)
    _ ≤ ∑ M ∈ Finset.range (Nat.log 2 X + 1), (shellBad S M).card :=
      Finset.card_biUnion_le
end FirstPassageLinearTransport
