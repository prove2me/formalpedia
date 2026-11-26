-- Prove2me | solution 1 for FirstPassageLinearTransport.collatzThreeBlockEnvelopeEvent_of_full
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:57:06.154822+00:00
-- url     : https://prove2.me/submissions/c1770507-b2dc-4637-bf7a-4b1c18d438a0

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Theorems.Thm_FirstPassageLinearTransport_wordIncrementSum_neg
import Theorems.Thm_FirstPassageLinearTransport_listIncrementSum_reverse
import Theorems.Thm_FirstPassageLinearTransport_listSurvivesFrom_append
import Theorems.Thm_FirstPassageLinearTransport_listSurvivesFrom_reverse_neg
import Theorems.Thm_FirstPassageLinearTransport_wordSurvivesFrom_iff_list
import Theorems.Thm_FirstPassageLinearTransport_ofFn_rev
import Theorems.Thm_FirstPassageLinearTransport_wordIncrementSum_eq_list
import Theorems.Thm_FirstPassageLinearTransport_wordIncrementSum_collatzThreeBlockWord
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
    {a b : ℕ} {B q : ℝ}
    {u : Fin a → Bool} {v : Fin b → Bool} {w : Fin a → Bool}
    (hfull : collatzFullBarrierBinEvent B q
      (collatzThreeBlockWord u v w)) :
    collatzThreeBlockEnvelopeEvent B q u v w := by
  rcases hfull with ⟨hsurv, hterminal⟩
  have hslist : listSurvivesFrom (-B) collatzLogIncrement 0
      (List.ofFn u ++ List.ofFn v ++ (List.ofFn w).reverse) := by
    have h := (wordSurvivesFrom_iff_list (-B) collatzLogIncrement 0
      (collatzThreeBlockWord u v w)).mp hsurv
    simpa [collatzThreeBlockWord, ofFn_rev, List.append_assoc] using h
  have hfirstList : listSurvivesFrom (-B) collatzLogIncrement 0
      (List.ofFn u) :=
    ((listSurvivesFrom_append (-B) collatzLogIncrement 0
      (List.ofFn u) (List.ofFn v ++ (List.ofFn w).reverse)).mp
        (by simpa [List.append_assoc] using hslist)).1
  have hfirst : wordSurvivesFrom (-B) collatzLogIncrement a 0 u :=
    (wordSurvivesFrom_iff_list (-B) collatzLogIncrement 0 u).mpr
      hfirstList
  have hterminal' :
      q - B ≤ wordIncrementSum collatzLogIncrement u +
          wordIncrementSum collatzLogIncrement v +
          wordIncrementSum collatzLogIncrement w ∧
        wordIncrementSum collatzLogIncrement u +
          wordIncrementSum collatzLogIncrement v +
          wordIncrementSum collatzLogIncrement w < q - B + 1 := by
    simpa [collatzMiddleInterval, wordIncrementSum_collatzThreeBlockWord]
      using hterminal
  have htotalList :
      listIncrementSum collatzLogIncrement
          (List.ofFn u ++ List.ofFn v ++ (List.ofFn w).reverse) <
        q - B + 1 := by
    rw [listIncrementSum_append, listIncrementSum_append,
      listIncrementSum_reverse, ← wordIncrementSum_eq_list,
      ← wordIncrementSum_eq_list, ← wordIncrementSum_eq_list]
    linarith [hterminal'.2]
  have hrevList := listSurvivesFrom_reverse_neg hslist
    (hi := q - B + 1) (by simpa using htotalList)
  have hrevList' :
      listSurvivesFrom (-(q + 1))
        (fun bit => -collatzLogIncrement bit) 0
        (List.ofFn w ++
          ((List.ofFn v).reverse ++ (List.ofFn u).reverse)) := by
    convert hrevList using 1
    · ring
    · simp [List.reverse_append, List.append_assoc]
  have hlastList :
      listSurvivesFrom (-(q + 1))
        (fun bit => -collatzLogIncrement bit) 0 (List.ofFn w) :=
    ((listSurvivesFrom_append (-(q + 1))
      (fun bit => -collatzLogIncrement bit) 0 (List.ofFn w)
      ((List.ofFn v).reverse ++ (List.ofFn u).reverse)).mp hrevList').1
  have hlast :
      wordSurvivesFrom (-(q + 1))
        (fun bit => -collatzLogIncrement bit) a 0 w :=
    (wordSurvivesFrom_iff_list (-(q + 1))
      (fun bit => -collatzLogIncrement bit) 0 w).mpr hlastList
  refine ⟨hfirst, hlast, ?_⟩
  unfold collatzMiddleInterval
  rw [wordIncrementSum_neg]
  constructor <;> linarith [hterminal'.1, hterminal'.2]
end FirstPassageLinearTransport
