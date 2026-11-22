-- Prove2me | solution 1 for DeciSigma1.Full.Closure.Neg.word_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:08:41.625958+00:00
-- url     : https://prove2.me/submissions/8ebf59c0-aa22-4c01-92eb-380a3cd4d362

module
public import Mathlib.Data.Fintype.Powerset
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Constraints
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Automata

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Closure
open DeciSigma1.Automata
open DeciSigma1.Constraints
variable {n : ℕ} {V : Type*}
namespace DeciSigma1.Full.Closure
namespace Neg
theorem _root_.solution {Γ : List (LitT n V)} {n : Config n V} (h : Neg Γ n) :
    n.2.2 = [] := by cases h <;> rfl
end Neg
end DeciSigma1.Full.Closure
