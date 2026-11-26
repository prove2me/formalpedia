-- Prove2me | solution 1 for FirstPassageLinearTransport.multiplicativeHitCount_of_crossed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:58:10.313314+00:00
-- url     : https://prove2.me/submissions/ddf6521b-83b0-4d02-961b-956e028b9207

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Theorems.Thm_FirstPassageLinearTransport_crossesMultiplicativeFrom_of_crossed
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
    {u z : ℝ} {r : ℕ} (hz : u < z) :
    multiplicativeHitCount u r z = 2 ^ r := by
  classical
  rw [multiplicativeHitCount]
  have hfilter :
      Finset.univ.filter (crossesMultiplicativeFrom u r z) = Finset.univ := by
    exact Finset.filter_eq_self.mpr
      (fun v _ => crossesMultiplicativeFrom_of_crossed hz v)
  rw [hfilter]
  simp
end FirstPassageLinearTransport
