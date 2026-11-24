-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x6.lev_uh
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:54:12.632027+00:00
-- url     : https://prove2.me/submissions/618dc103-89fc-46e7-81a2-be41a9665fbf

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_herm3
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_uh_of_herm
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lev_mulVec_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lev_mulVec_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lev_mulVec_res
import Theorems.Thm_Formalism_QuantumDeterminants_ggHerm_unitary


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
theorem _root_.solution {g : Mat k r'} (hg : g ∈ UH (Hpk k r')) : ιLev k 1 r' g ∈ UH (Hpk k (1 + r')) := by
  apply uh_of_herm
  intro u w
  rw [herm3, herm3 u w, lev_mulVec_F, lev_mulVec_F, lev_mulVec_L, lev_mulVec_L, lev_mulVec_res, lev_mulVec_res,
    ggHerm_unitary _ _ hg]
end Formalism.FourierDecayAlt.P.B2x6
