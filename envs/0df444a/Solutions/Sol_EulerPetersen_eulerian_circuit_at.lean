-- Prove2me | solution 1 for EulerPetersen.eulerian_circuit_at
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:09:46.292063+00:00
-- url     : https://prove2.me/submissions/2061746c-e818-4f0c-aa0b-73040539d9ae

module
public import Definitions.Def_Euler
public import Definitions.Def_EulerPetersen_Solution
public import Theorems.Thm_SimpleGraph_exists_isEulerian_circuit_at


set_option autoImplicit true
@[expose] public section
public section
open EulerPetersen
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
namespace EulerPetersen
theorem _root_.solution (hconn : G.Connected) (heven : ∀ v, Even (G.degree v)) (a : V) :
    ∃ p : G.Walk a a, p.IsEulerian :=
  SimpleGraph.exists_isEulerian_circuit_at hconn heven a
end EulerPetersen
