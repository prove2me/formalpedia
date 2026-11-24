-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux1.cdm_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:12:06.525719+00:00
-- url     : https://prove2.me/submissions/07bd89d6-c767-48e0-9b60-917c1ac23883

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleyForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactlySupportedBanachModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_cdm_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_cd_det
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_cdm_updateRow

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
theorem _root_.solution {F : X → Mat k r} (hF : ContDiffOn ℝ n F s) (hu : ∀ x ∈ s, IsUnit (F x).det) :
    ContDiffOn ℝ n (fun x => (F x)⁻¹) s := by
  rw [cdm_iff]
  intro i j
  have e : (fun x => (F x)⁻¹ i j)
      = fun x => ((F x).det)⁻¹ * ((F x).updateRow j (Pi.single i 1)).det := by
    funext x
    rw [Matrix.inv_def, Matrix.smul_apply, adjugate_apply, Ring.inverse_eq_inv', smul_eq_mul]
  rw [e]
  exact ((cd_det hF).inv fun x hx => (hu x hx).ne_zero).mul (cd_det (cdm_updateRow hF j _))
end Formalism.FourierDecayAlt.P.Ux1
