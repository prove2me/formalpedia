-- Prove2me | solution 1 for DeciSigma1.Full.Closure.Fact.word_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:08:35.391641+00:00
-- url     : https://prove2.me/submissions/9da04724-4d04-46ef-b30b-247f4318b6d4

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
namespace Fact
theorem _root_.solution {Γ : List (LitT n V)} {f : Config n V} (h : Fact Γ f) :
    f.2.2 = [] := by cases h <;> rfl
end Fact
end DeciSigma1.Full.Closure
