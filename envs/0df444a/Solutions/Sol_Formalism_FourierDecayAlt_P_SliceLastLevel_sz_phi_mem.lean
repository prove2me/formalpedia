-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SliceLastLevel.sz_phi_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:39:40.460537+00:00
-- url     : https://prove2.me/submissions/72fb0bde-78c3-4c59-88a3-ac693fdb11d8

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiBoundPartsOfRadicalParametrisation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LongWeylElement
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SettingExistence
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothnessOnGoodSet
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SliceLastLevel
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_sz_N_GV
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_sz_N_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_sz_castW_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gv_mul
import Theorems.Thm_Formalism_QuantumDeterminants_big_cell_mem_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SliceLastLevel
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.Ux5
namespace Formalism.FourierDecayAlt.P.SliceLastLevel
theorem _root_.solution {k r : ℕ} (c : Fin r → ℂ) (hc : ∀ a, c a ≠ 0) {n n' : B.Mat k r} (hn : n ∈ Nset k r)
    (hn' : n' ∈ Nset k r) {μ : B.Mat k 0} (hμ : μ ∈ B.GV k 0) : phi k r c n n' μ ∈ B.GV k r := by
  unfold phi
  exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (sz_N_GV (sz_N_inv hn))
    (big_cell_mem_holds k r c (castW μ) hc (sz_castW_mem μ hμ))) (sz_N_GV hn')
end Formalism.FourierDecayAlt.P.SliceLastLevel
