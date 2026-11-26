-- Prove2me | solution 1 for DenseTriangleFree.slotProj_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:48:47.226728+00:00
-- url     : https://prove2.me/submissions/1b3d42d3-b3da-4e5f-92de-9228b7114e0a

module
public import Definitions.Def_JinLib_Grotzsch
public import Definitions.Def_JinLib_Blowup

set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree
open SimpleGraph
namespace DenseTriangleFree
theorem _root_.solution : ∀ x : Fin 11,
    (Finset.univ.filter fun k : Fin 29 => grotzsch.Adj x (slotProj k)).card = 10 := by
  decide
end DenseTriangleFree
