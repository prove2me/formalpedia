-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x9.grp_mem_PPsub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:52:14.664092+00:00
-- url     : https://prove2.me/submissions/ad24a06d-aa55-401c-adf8-580a00837b35

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x9
noncomputable section
variable {K : Type} [CommRing K] (R : Subring K) (k : ℕ)
namespace Formalism.FourierDecayAlt.P.A5x9
theorem _root_.solution {N : ℕ} (u : upUniG K N) :
    u ∈ PPsub R k N ↔ IsPP R k ((u : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) := Iff.rfl
end Formalism.FourierDecayAlt.P.A5x9
