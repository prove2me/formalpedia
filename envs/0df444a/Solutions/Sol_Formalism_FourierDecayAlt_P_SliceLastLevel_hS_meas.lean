-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SliceLastLevel.hS_meas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:58:01.069049+00:00
-- url     : https://prove2.me/submissions/533bd2d8-ae13-4cf0-bb6b-6a994d99f127

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_phi_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_nset_gv
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_Sn_closed
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_phi_contOn
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_continuousOn_of_contDiffOn_group


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SliceLastLevel
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]
namespace Formalism.FourierDecayAlt.P.SliceLastLevel
theorem _root_.solution {F : B.Mat k r → (Wq →L[ℂ] Wp)} {m : ℕ∞} (hF : B.CkOn m (B.GV k r) F) {c : Fin r → ℂ}
    (hc : ∀ a, c a ≠ 0) (μN : Measure (Mt k r × Mt k r)) {g : B.Mat k 0} (hg : g ∈ B.GV k 0) :
    AEStronglyMeasurable (fun ξ => hS F c ξ g) μN := by
  have hcont : ContinuousOn (fun ξ : Mt k r × Mt k r => F (phi k r c (Matrix.of ξ.1) (Matrix.of ξ.2) g)) (Sn k r) :=
    (Formalism.FourierDecayAlt.P.B6.continuousOn_of_contDiffOn_group hF).comp (phi_contOn c g)
      (fun ξ hξ => phi_mem hc (nset_gv hξ.1) (nset_gv hξ.2) hg)
  exact (aestronglyMeasurable_indicator_iff Sn_closed.measurableSet).2
    (hcont.aestronglyMeasurable Sn_closed.measurableSet)
end Formalism.FourierDecayAlt.P.SliceLastLevel
