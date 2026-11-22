-- Prove2me | solution 1 for DeciSigma1.Automata.derivedPairs_refl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:35:02.258936+00:00
-- url     : https://prove2.me/submissions/365965a3-fa30-42e3-8d98-6eaa1b0c7406

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
theorem _root_.solution (Γ : List (LitT n V)) (x : V) : (x, x) ∈ derivedPairs Γ :=
  (mem_derivedPairs Γ x x).mpr (.refl x)
end DeciSigma1.Automata
