-- Prove2me | solution 1 for FirstPassageLinearTransport.listSurvivesFrom_reverse_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:54:45.9903+00:00
-- url     : https://prove2.me/submissions/e50b85c1-a831-42bd-b21e-d928f07db195

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Theorems.Thm_FirstPassageLinearTransport_listIncrementSum_neg
import Theorems.Thm_FirstPassageLinearTransport_listIncrementSum_reverse
import Theorems.Thm_FirstPassageLinearTransport_listSurvivesFrom_initial
import Theorems.Thm_FirstPassageLinearTransport_listSurvivesFrom_append
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
    {lo hi z : ℝ} {x : Bool → ℝ} {l : List Bool}
    (hs : listSurvivesFrom lo x z l)
    (ht : z + listIncrementSum x l < hi) :
    listSurvivesFrom (lo - hi) (fun b => -x b) 0 l.reverse := by
  induction l generalizing z with
  | nil =>
      have hz : lo ≤ z := hs
      rw [listIncrementSum_nil] at ht
      change lo - hi ≤ 0
      linarith
  | cons b l ih =>
      rcases hs with ⟨hz, hs⟩
      rw [List.reverse_cons, listSurvivesFrom_append]
      have ht' : z + x b + listIncrementSum x l < hi := by
        simpa [listIncrementSum_cons, add_assoc] using ht
      have hrev := ih hs ht'
      constructor
      · exact hrev
      · have hstart := listSurvivesFrom_initial hs
        have hbefore : listIncrementSum x l + lo ≤ hi := by
          linarith
        have hfinal : listIncrementSum x l + (lo - hi) ≤ -x b := by
          linarith
        simpa [listSurvivesFrom, listIncrementSum_reverse,
          listIncrementSum_neg, add_comm, add_left_comm, add_assoc] using
            And.intro hbefore hfinal
end FirstPassageLinearTransport
