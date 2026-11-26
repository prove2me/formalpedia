-- Prove2me | solution 1 for FirstPassageLinearTransport.barrierHitCount_of_bad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:22:08.532608+00:00
-- url     : https://prove2.me/submissions/07eb1afd-41e1-49d0-a322-00cb6eb867b3

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_FirstPassageLinearTransport_Parity
import Definitions.Def_FirstPassageLinearTransport_Density
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Theorems.Thm_FirstPassageLinearTransport_hitsBarrierFrom_of_bad
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero



set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
namespace FirstPassageLinearTransport
theorem _root_.solution {a : ℝ} {r : ℕ} {y : ℤ}
    (hy : a < |(y : ℝ)|) :
    barrierHitCount a r y = 2 ^ r := by
  classical
  rw [barrierHitCount]
  have hfilter :
      Finset.univ.filter (hitsBarrierFrom a r y) = Finset.univ := by
    exact Finset.filter_eq_self.mpr (fun v _ => hitsBarrierFrom_of_bad hy v)
  rw [hfilter]
  simp
end FirstPassageLinearTransport
