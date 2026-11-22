-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.runPrefix_period_stable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:00:50.492809+00:00
-- url     : https://prove2.me/submissions/7aecd994-edb4-4d47-918e-857e85f756c9

module
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_FinitePaths
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Levels
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_TerminalRays
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Arithmetic_runFrom_take_periodic
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthBound_nil
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthEnvelope_nil
public import Theorems.Thm_DeciSigma1_Readers_Table_runPrefix_add
public import Theorems.Thm_DeciSigma1_Words_Ray_length_suffixBeforeOnset
public import Theorems.Thm_DeciSigma1_Words_length_suffixOfLength
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_cons_cons
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_nil
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_singleton
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.Holes.Tail.suffixLengthBound_nil
attribute [local simp] DeciSigma1.Holes.Tail.suffixLengthEnvelope_nil
attribute [local simp] DeciSigma1.Words.Ray.length_suffixBeforeOnset
attribute [local simp] DeciSigma1.Words.length_suffixOfLength
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Automata DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}
namespace DeciSigma1.Holes.Tail
theorem _root_.solution [Fintype S] (T : Table α S k) (W : Fin k → List α) (i : Fin k)
    {p s e x : ℕ} (hp : 0 < p) (hper : PeriodicOn (W i) p s e) (he : e ≤ (W i).length)
    (hx : s + Fintype.card S * p ≤ x) (hxe : x + p * (Fintype.card S).factorial ≤ e) :
    T.runPrefix W i (x + p * (Fintype.card S).factorial) = T.runPrefix W i x := by
  set u := ((W i).drop s).take (e - s) with hu
  have hulen : u.length = e - s := by simp only [hu, List.length_take, List.length_drop]; omega
  have hperu : PeriodicOn u p 0 u.length := by
    intro j _ hj
    rw [hulen] at hj
    simp only [hu, List.getElem?_take, List.getElem?_drop]
    rw [if_pos (by omega), if_pos (by omega), show s + (j + p) = (s + j) + p by ring]
    exact hper (s + j) (by omega) (by omega)
  have hutake : ∀ t ≤ e - s, ((W i).drop s).take t = u.take t := by
    intro t ht; rw [hu, List.take_take, min_eq_left ht]
  have key :=
      Arithmetic.runFrom_take_periodic T (T.runPrefix W i s) hp hperu (o := x - s) (by omega) 1
    (by rw [hulen]; omega)
  rw [show x + p * (Fintype.card S).factorial =
      s + (x - s + 1 * (p * (Fintype.card S).factorial)) by omega,
    Table.runPrefix_add, hutake _ (by omega), key, ← hutake _ (by omega), ← Table.runPrefix_add,
    show s + (x - s) = x by omega]
end DeciSigma1.Holes.Tail
