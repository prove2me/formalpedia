-- Prove2me | solution 1 for EulerPetersen.eulerian_orientation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:09:41.762027+00:00
-- url     : https://prove2.me/submissions/5bd350c2-e3d7-45dc-b14c-45decbaf6fe2

module
public import Definitions.Def_Euler
public import Definitions.Def_EulerPetersen_Solution
public import Theorems.Thm_SimpleGraph_exists_balanced_orientation


set_option autoImplicit true
@[expose] public section
public section
open EulerPetersen
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
namespace EulerPetersen
theorem _root_.solution (heven : ∀ v, Even (G.degree v)) :
    ∃ Ds : Finset G.Dart, (∀ d ∈ Ds, ∀ d' ∈ Ds, d.edge = d'.edge → d = d') ∧
      (∀ v, (Ds.filter fun d => d.fst = v).card = (Ds.filter fun d => d.snd = v).card) ∧
      ∀ e ∈ G.edgeSet, ∃ d ∈ Ds, d.edge = e :=
  SimpleGraph.exists_balanced_orientation heven
end EulerPetersen
