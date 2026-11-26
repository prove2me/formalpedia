-- Prove2me | solution 1 for FirstPassageLinearTransport.listSurvivesFrom_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:34:10.376675+00:00
-- url     : https://prove2.me/submissions/3ca23baf-0883-4800-bb3f-385f48f3b36f

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Theorems.Thm_FirstPassageLinearTransport_listSurvivesFrom_initial
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
theorem _root_.solution (lo : ℝ) (x : Bool → ℝ)
    (z : ℝ) (l r : List Bool) :
    listSurvivesFrom lo x z (l ++ r) ↔
      listSurvivesFrom lo x z l ∧
        listSurvivesFrom lo x (z + listIncrementSum x l) r := by
  induction l generalizing z with
  | nil =>
      constructor
      · intro h
        exact ⟨listSurvivesFrom_initial h, by simpa using h⟩
      · rintro ⟨_hz, h⟩
        simpa using h
  | cons b l ih =>
      simp only [List.cons_append, listSurvivesFrom,
        listIncrementSum_cons]
      change
        (lo ≤ z ∧ listSurvivesFrom lo x (z + x b) (l ++ r)) ↔
          (lo ≤ z ∧ listSurvivesFrom lo x (z + x b) l) ∧
            listSurvivesFrom lo x
              (z + (x b + listIncrementSum x l)) r
      rw [ih (z + x b)]
      constructor
      · rintro ⟨hz, hl, hr⟩
        exact ⟨⟨hz, hl⟩, by convert hr using 1 <;> ring⟩
      · rintro ⟨⟨hz, hl⟩, hr⟩
        exact ⟨hz, hl, by convert hr using 1 <;> ring⟩
end FirstPassageLinearTransport
