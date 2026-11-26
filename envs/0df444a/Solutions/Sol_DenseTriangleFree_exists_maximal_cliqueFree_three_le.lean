-- Prove2me | solution 1 for DenseTriangleFree.exists_maximal_cliqueFree_three_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:48:19.237464+00:00
-- url     : https://prove2.me/submissions/68b9ba4b-d722-4a8e-ad57-9a32bff966df

module
public import Mathlib
public import Definitions.Def_JinLib_Grotzsch
public import Definitions.Def_JinLib_Maximal

set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree
open SimpleGraph
variable {V : Type*}
namespace DenseTriangleFree
theorem _root_.solution [Finite V] {G : SimpleGraph V} (h3 : G.CliqueFree 3) :
    ∃ G' : SimpleGraph V, G ≤ G' ∧ Maximal (fun H : SimpleGraph V => H.CliqueFree 3) G' := by
  obtain ⟨G', hle, hmax⟩ :=
    (Set.toFinite {H : SimpleGraph V | H.CliqueFree 3}).exists_le_maximal (a := G) h3
  exact ⟨G', hle, hmax⟩
end DenseTriangleFree
