-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.assemble_diagonal_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:55:28.438545+00:00
-- url     : https://prove2.me/submissions/260b86d0-7f66-4f2c-9b1b-3011a3a57cde

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_diagDom
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_betaTau_self
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_InCC_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_core

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.B.AssembleDiag := by
  intro hC hAe hFa hL hDC k r Wp Wq _ _ _ _ _ _ D A hA hRB hRA hU hJ hDB
  have hDD : DiagDom D A := diagDom hAe hFa hRB hRA hU hJ
  refine ⟨hDD, ?_⟩
  intro F hF τ hτ
  have hF4 : InCC A 4 F := InCC_mono (by norm_num) hF
  refine ⟨ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hDD F hF4 τ hτ).2, ?_⟩
  rw [← betaTau_self hJ hF4 hτ]
  exact core hC hAe hFa hL hDC hA hRB hRA hU hJ hDB hτ F F hF hF
end Formalism.FourierDecayAlt.P
