-- Prove2me | solution 1 for DeciSigma1.Automata.Semiautomaton.short_safe_path
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:10:57.899685+00:00
-- url     : https://prove2.me/submissions/c67a2f92-4f41-41f7-8dc5-81d2694888bd

module
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.Card
public import Mathlib.Computability.DFA
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Basic
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_append
public import Theorems.Thm_DeciSigma1_runFrom_snoc
public import Theorems.Thm_DeciSigma1_Automata_Semiautomaton_pathSafe_append
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_snoc

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Automata
variable {α : Type*}
open DeciSigma1.Automata.Semiautomaton
variable {S : Type*}
namespace DeciSigma1.Automata.Semiautomaton
theorem _root_.solution [Fintype S] (M : Semiautomaton α S) (G : S → Prop) (q : S)
    (w : Word α) (h : M.PathSafe G q w) :
    ∃ v, v.length < Fintype.card S ∧ M.PathSafe G q v ∧
      runFrom M.step q v = runFrom M.step q w := by
  induction hw : w.length using Nat.strong_induction_on generalizing w with
  | h n ih =>
    by_cases hn : w.length < Fintype.card S
    · exact ⟨w, hn, h, rfl⟩
    · let A : DFA α S := ⟨M.step, q, Set.univ⟩
      obtain ⟨r, a, b, c, he, _, hb, ha, hloop, hc⟩ :=
        A.evalFrom_split (s := q) (x := w) (t := runFrom M.step q w) (by omega) rfl
      change runFrom M.step q a = r at ha
      change runFrom M.step r b = r at hloop
      change runFrom M.step r c = runFrom M.step q w at hc
      have hs := h
      rw [he, pathSafe_append, pathSafe_append] at hs
      have hs' : M.PathSafe G q (a ++ c) := by
        apply (pathSafe_append M G q a c).mpr
        refine ⟨hs.1.1, ?_⟩
        have heq : runFrom M.step q (a ++ b) = runFrom M.step q a := by
          rw [runFrom_append, ha, hloop]
        simpa [heq] using hs.2
      have hlen : (a ++ c).length < n := by
        have hbpos := List.length_pos_iff.mpr hb
        simp only [he, List.length_append] at hw
        simp only [List.length_append]
        omega
      obtain ⟨v, hv, hvs, hve⟩ := ih _ hlen (a ++ c) hs' rfl
      exact ⟨v, hv, hvs, hve.trans (by rw [runFrom_append, ha, hc])⟩
end DeciSigma1.Automata.Semiautomaton
