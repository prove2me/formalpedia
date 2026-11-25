-- Prove2me | solution 1 for EulerPetersen.eulerian_circuit_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:53:27.721398+00:00
-- url     : https://prove2.me/submissions/2b96efa3-5e56-4d51-8988-3e91e23b3cae

module
public import Definitions.Def_Euler
public import Definitions.Def_EulerPetersen_Solution
public import Theorems.Thm_SimpleGraph_exists_isEulerian_iff_forall_even_degree


set_option autoImplicit true
@[expose] public section
public section
open EulerPetersen
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
namespace EulerPetersen
theorem _root_.solution (hconn : G.Connected) :
    (∃ u, ∃ p : G.Walk u u, p.IsEulerian) ↔ ∀ v, Even (G.degree v) :=
  SimpleGraph.exists_isEulerian_iff_forall_even_degree hconn
end EulerPetersen
