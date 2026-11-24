-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux1.cd_co
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:35:19.93592+00:00
-- url     : https://prove2.me/submissions/331991fc-07e5-486e-a38f-917d651f39c7

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleyForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactlySupportedBanachModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_cdm_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux1
theorem _root_.solution {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : WithTop ℕ∞} {s : Set X}
    {F : X → Mat k r} (hF : ContDiffOn ℝ n F s) (i : J k r) : ContDiffOn ℝ n (fun x => co (F x) i) s := by
  rw [cdm_iff] at hF
  unfold co
  by_cases h : i.2.2 = true
  · simp only [h, if_true]; exact Complex.imCLM.contDiff.comp_contDiffOn (hF _ _)
  · simp only [h]; exact Complex.reCLM.contDiff.comp_contDiffOn (hF _ _)
end Formalism.FourierDecayAlt.P.Ux1
