-- Prove2me | solution 1 for DeciSigma1.Automata.derivedPairs_trans
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:35:08.579436+00:00
-- url     : https://prove2.me/submissions/13ce1553-b181-4b03-86ee-7e2b574174d0

module
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Constraints
public import Theorems.Thm_DeciSigma1_Constraints_mem_derivedPairs


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1
open DeciSigma1.Constraints
open DeciSigma1.Automata
variable {n : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
namespace DeciSigma1.Automata
theorem _root_.solution {Γ : List (LitT n V)} {x y z : V}
    (h : (x, y) ∈ derivedPairs Γ) (h' : (y, z) ∈ derivedPairs Γ) : (x, z) ∈ derivedPairs Γ :=
  (mem_derivedPairs Γ x z).mpr
    (.trans ((mem_derivedPairs Γ x y).mp h) ((mem_derivedPairs Γ y z).mp h'))
end DeciSigma1.Automata
