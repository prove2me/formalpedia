-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PairingConjugationLemmas.eD_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:37:02.156077+00:00
-- url     : https://prove2.me/submissions/fb1831d0-f1e7-4aa8-b436-c80f74104613

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
theorem _root_.solution (m : Fin (finrank ℤ La) → ℤ) : ((eD La m : dualSet La) : V f) = ψd La m := rfl
end Formalism.FourierDecayAlt.P.PairingConjugationLemmas
