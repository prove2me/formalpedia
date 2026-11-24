-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x3.Grp.val_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:47:16.590477+00:00
-- url     : https://prove2.me/submissions/08d8fff1-2a19-45a3-ac1d-44bc20bee530

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x3
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open Formalism.FourierDecayAlt.P.B2x3.Grp
variable {k r : ℕ} {U : Set (Mat k r)} {h : IsClosedSubgroup U}
namespace Formalism.FourierDecayAlt.P.B2x3.Grp
theorem _root_.solution (a b : Grp U h) : (a * b).val = a.val * b.val := rfl
end Formalism.FourierDecayAlt.P.B2x3.Grp
