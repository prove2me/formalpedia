-- Prove2me | solution 1 for CompactnessConjecture.symplecticQuadrangle_encodeFiniteGraph_free_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:02.568649+00:00
-- url     : https://prove2.me/submissions/ca0613f9-5193-442c-b6b1-f0e6f3a4f715

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable (K : Type*) [Field K]
namespace CompactnessConjecture
theorem _root_.solution
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) :
    (encodeFiniteGraph G).graph.Free
        (symplecticQuadrangle K) ↔
      G.Free (symplecticQuadrangle K) :=
  (SimpleGraph.free_congr_left
    (SimpleGraph.Iso.map (Fintype.equivFin V) G)).symm
end CompactnessConjecture
