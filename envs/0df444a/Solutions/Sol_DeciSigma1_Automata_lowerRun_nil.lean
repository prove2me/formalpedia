-- Prove2me | solution 1 for DeciSigma1.Automata.lowerRun_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:19:54.677446+00:00
-- url     : https://prove2.me/submissions/178786f9-0705-4d3e-8d44-808542c70146

module
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Constraints

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1
open DeciSigma1.Constraints
open DeciSigma1.Automata
variable {n : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
namespace DeciSigma1.Automata
theorem _root_.solution (Γ : List (LitT n V)) (x : V) : lowerRun Γ x [] = down Γ x := rfl
end DeciSigma1.Automata
