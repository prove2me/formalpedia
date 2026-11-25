-- Prove2me | solution 1 for EulerPetersen.petersen_two_factor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:20:18.028072+00:00
-- url     : https://prove2.me/submissions/fc0f7ce2-d6bb-44cb-a19b-c2a5eb4b2513

module
public import Definitions.Def_Euler
public import Definitions.Def_EulerPetersen_Solution
public import Theorems.Thm_SimpleGraph_petersen_two_factor


set_option autoImplicit true
@[expose] public section
public section
open EulerPetersen
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
namespace EulerPetersen
theorem _root_.solution (k : ℕ) (h : ∀ v, G.degree v = 2 * k) :
    ∃ F : Fin k → SimpleGraph V, (∀ i, F i ≤ G) ∧
      (∀ i v, ((F i).neighborSet v).ncard = 2) ∧
      (∀ i j, i ≠ j → Disjoint (F i) (F j)) ∧ ⨆ i, F i = G :=
  SimpleGraph.petersen_two_factor k h
end EulerPetersen
