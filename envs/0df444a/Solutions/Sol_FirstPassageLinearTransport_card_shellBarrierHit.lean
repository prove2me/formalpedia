-- Prove2me | solution 1 for FirstPassageLinearTransport.card_shellBarrierHit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:25:41.331325+00:00
-- url     : https://prove2.me/submissions/fb3c302e-6c75-4c6a-af05-a0371fe09db7

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_FirstPassageLinearTransport_Parity
import Definitions.Def_FirstPassageLinearTransport_Density
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Theorems.Thm_FirstPassageLinearTransport_card_barrierResidues
import Theorems.Thm_FirstPassageLinearTransport_boolParityWord_mod
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_card_dyadicShell_filter_mod_mem
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


attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
namespace FirstPassageLinearTransport
theorem _root_.solution (M : ℕ) (h : ℝ) :
    (shellBarrierHit M h).card = barrierHitCount (2 * h) M 0 := by
  classical
  have heq :
      shellBarrierHit M h =
        (dyadicShell M).filter
          (fun n =>
            (⟨n % (2 ^ M), Nat.mod_lt _ (pow_pos (by omega) _)⟩ :
              Fin (2 ^ M)) ∈ barrierResidues M h) := by
    ext n
    simp only [shellBarrierHit, barrierResidues, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact and_congr_right (fun _ => by
      rw [boolParityCode_eq_word, boolParityWord_mod])
  rw [heq, card_dyadicShell_filter_mod_mem, card_barrierResidues]
end FirstPassageLinearTransport
