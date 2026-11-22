-- Prove2me | solution 1 for DeciSigma1.Full.Closure.lowest_point_leaf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:07:24.433477+00:00
-- url     : https://prove2.me/submissions/51606300-83fb-457c-a961-a822213cbb6f

module
public import Mathlib.Data.Fintype.Powerset
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Constraints
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Automata
public import Theorems.Thm_DeciSigma1_Full_Closure_moves_iff_signed
public import Theorems.Thm_DeciSigma1_Automata_lowest_point


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Closure
open DeciSigma1.Semantics DeciSigma1.Constraints
variable {n : ℕ} {V : Type*}
variable {c : Fin n → Bool} {Γ : List (LitT n V)}
variable [Fintype V] [DecidableEq V]
namespace DeciSigma1.Full.Closure
theorem _root_.solution {p q : V} {s s' : Bool} {u t : List (Fin n)} :
    Relation.ReflTransGen (Move c Γ) (p, s, u) (q, s', t) ↔
      ∃ i ≤ u.length, ∃ e ≤ t.length, u.drop i = t.drop e ∧
        (Automata.upperRun (signed c Γ) (p, s) (u.take i) ∩
          Automata.lowerRun (signed c Γ) (q, s') (t.take e)).Nonempty := by
  rw [moves_iff_signed]
  exact Automata.lowest_point
end DeciSigma1.Full.Closure
