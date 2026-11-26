-- Prove2me | solution 1 for BKAR.AcyclicEdgeSetData.inSameComponent_trans
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:04:59.842654+00:00
-- url     : https://prove2.me/submissions/c04b78a8-05f5-4d9d-b2fd-490e3c01c2dd

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Definitions.Def_BKAR_Forest
import Definitions.Def_BKAR_ForestGraph
import Theorems.Thm_BKAR_AcyclicEdgeSetData_inSameComponent_iff_exists_isSimplePath


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.AcyclicEdgeSetData
open EdgePath
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.AcyclicEdgeSetData
theorem _root_.solution
    {S : Finset (Edge V)} (data : AcyclicEdgeSetData S)
    {i j k : V} (hij : data.inSameComponent i j)
    (hjk : data.inSameComponent j k) :
    data.inSameComponent i k := by
  rcases data.inSameComponent_iff_exists_isSimplePath.mp hij with
    ⟨γij, hγij⟩
  rcases data.inSameComponent_iff_exists_isSimplePath.mp hjk with
    ⟨γjk, hγjk⟩
  rcases hγij.1.exists_walk with ⟨pij, _hpij⟩
  rcases hγjk.1.exists_walk with ⟨pjk, _hpjk⟩
  exact data.inSameComponent_of_edgeSetGraph_reachable
    (SimpleGraph.Reachable.trans ⟨pij⟩ ⟨pjk⟩)
end BKAR.AcyclicEdgeSetData
