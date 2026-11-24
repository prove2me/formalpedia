-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux1.cdm_updateRow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:35:18.266504+00:00
-- url     : https://prove2.me/submissions/7a763a8f-e270-4fab-a416-391417c4eb25

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
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : WithTop ℕ∞} {s : Set X}
namespace Formalism.FourierDecayAlt.P.Ux1
theorem _root_.solution {F : X → Mat k r} (hF : ContDiffOn ℝ n F s) (j : Fin (2 * r + k + 1))
    (b : Fin (2 * r + k + 1) → ℂ) : ContDiffOn ℝ n (fun x => (F x).updateRow j b) s := by
  rw [cdm_iff] at hF ⊢
  intro a l
  by_cases ha : a = j
  · subst ha; simp only [updateRow_self]; exact contDiffOn_const
  · simp only [updateRow_ne ha]; exact hF a l
end Formalism.FourierDecayAlt.P.Ux1
