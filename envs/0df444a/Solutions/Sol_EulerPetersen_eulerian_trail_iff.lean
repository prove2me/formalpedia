-- Prove2me | solution 1 for EulerPetersen.eulerian_trail_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:14:21.434433+00:00
-- url     : https://prove2.me/submissions/f71eb72d-c940-476c-919e-2aaac8e6815c

module
public import Definitions.Def_Euler
public import Definitions.Def_EulerPetersen_Solution
public import Theorems.Thm_SimpleGraph_exists_isEulerian_walk_iff


set_option autoImplicit true
@[expose] public section
public section
open EulerPetersen
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
namespace EulerPetersen
theorem _root_.solution (hconn : G.Connected) :
    (∃ u v, ∃ p : G.Walk u v, p.IsEulerian) ↔
      Fintype.card {v | Odd (G.degree v)} = 0 ∨ Fintype.card {v | Odd (G.degree v)} = 2 :=
  SimpleGraph.exists_isEulerian_walk_iff hconn
end EulerPetersen
