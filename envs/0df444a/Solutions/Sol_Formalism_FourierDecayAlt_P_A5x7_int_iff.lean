-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x7.int_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:51:00.287337+00:00
-- url     : https://prove2.me/submissions/47a2f72d-0e76-4675-9270-07560094f699

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsIntOfLatOfLe
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsOpenIsIntSet
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x7_int_of_orb
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x7_orb_of_int
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x7_cos_eq_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x7
variable {K : Type} [CommRing K] (R : Subring K)
namespace Formalism.FourierDecayAlt.P.A5x7
theorem _root_.solution (w : Point K) (hw : InGLR R w) (q : Cos R w) :
    IsInt R (orbZ w (rep R q)) ↔ q = cos1 R w := by
  rw [cos_eq_iff]
  constructor
  · exact int_of_orb R w hw (rep R q)
  · rintro ⟨h1, h2⟩
    exact (orb_of_int R w hw (rep R q) h1 h2).1
end Formalism.FourierDecayAlt.P.A5x7
