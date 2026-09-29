-- Prove2me | solution 1 for Erdos180.proposedFamily_induction
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T02:26:48.932971+00:00
-- url     : https://prove2.me/submissions/ff187e6a-dbeb-4fa2-8486-248f667ac9cf

import Definitions.Def_erdos180_core4
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Data.Fintype.Sum
import Theorems.Thm_Erdos180_proposedFamily_mem_iff

open Erdos180
open Finset SimpleGraph

theorem solution {P : FiniteGraph → Prop}
    (hfour : P (finiteCycle 4)) (hsix : P (finiteCycle 6))
    (hj : ∀ f : JVertex → JVertex, JAdmissible f →
      P (encodeFiniteGraph (quotientGraph jTemplate f)))
    (hk : ∀ f : KVertex → KVertex, KAdmissible f →
      P (encodeFiniteGraph (quotientGraph kTemplate f))) :
    ∀ graph ∈ proposedFamily, P graph := by
  intro graph hgraph
  rcases proposedFamily_mem_iff.mp hgraph with
    ((rfl | rfl) | ⟨f, hf, rfl⟩) | ⟨f, hf, rfl⟩
  · exact hfour
  · exact hsix
  · exact hj f hf
  · exact hk f hf
