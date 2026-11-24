-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x6.iF_ne_iL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:12:57.707056+00:00
-- url     : https://prove2.me/submissions/0b7f7ae7-23fa-49c8-83bb-1de87c13d913

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_iF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_iL_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_iL_val


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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x6
theorem _root_.solution : iF k r' ≠ iL k r' := by
  intro h; have := congrArg Fin.val h; rw [iF_val, iL_val] at this; omega
end Formalism.FourierDecayAlt.P.B2x6
