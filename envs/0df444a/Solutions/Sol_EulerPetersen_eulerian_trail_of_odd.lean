-- Prove2me | solution 1 for EulerPetersen.eulerian_trail_of_odd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:09:29.376861+00:00
-- url     : https://prove2.me/submissions/9f60e4e7-b860-4218-876f-ca94319f378c

module
public import Definitions.Def_Euler
public import Definitions.Def_EulerPetersen_Solution
public import Theorems.Thm_SimpleGraph_exists_isEulerian_of_odd_iff


set_option autoImplicit true
@[expose] public section
public section
open EulerPetersen
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
namespace EulerPetersen
theorem _root_.solution (hconn : G.Connected) {a b : V} (hab : a ≠ b)
    (hodd : ∀ x, Odd (G.degree x) ↔ x = a ∨ x = b) : ∃ p : G.Walk a b, p.IsEulerian :=
  SimpleGraph.exists_isEulerian_of_odd_iff hconn hab hodd
end EulerPetersen
