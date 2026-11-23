-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PairingConjugationLemmas.repr_Tl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:37:17.398804+00:00
-- url     : https://prove2.me/submissions/aad08872-ad6d-41a3-8d2e-82daa604d41c

import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HerglotzLowerSemicontinuous
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PairingTriangular

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PairingConjugationLemmas
open MeasureTheory Filter Topology Finset Module Formalism.FourierDecayAlt.crystallineComparison
noncomputable section
variable {f : ℕ}
variable (La : Submodule ℤ (V f)) [DiscreteTopology La] [IsZLattice ℝ La]
namespace Formalism.FourierDecayAlt.P.PairingConjugationLemmas
theorem _root_.solution (y : Fin (finrank ℤ La) → ℝ) (j) : (bR La).repr (Tl La y) j = y j := by
  exact congrFun ((bR La).equivFun.apply_symm_apply y) j
end Formalism.FourierDecayAlt.P.PairingConjugationLemmas
