-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.lattice_of_local
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:01:33.315803+00:00
-- url     : https://prove2.me/submissions/e2a7a1f4-407c-4520-b847-b558be159b8c

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChebyshevToThreshold
import Theorems.Thm_Formalism_FourierDecayAlt_P_intersection_of_local

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.J.LatticeOfLocal := by
  intro E _ _ _ L hL Q _ pl M hcov hM
  have hint := intersection_of_local E L hL
  ext t
  rw [AddSubgroup.mem_iInf, Submodule.mem_toAddSubgroup, hint]
  constructor
  · intro h p
    rw [hM]
    intro P _ hP
    exact h P hP
  · intro h P hP
    obtain ⟨p, hp⟩ := hcov P hP
    exact (hM p t).mp (h p) P hp hP
end Formalism.FourierDecayAlt.P
