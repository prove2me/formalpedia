-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux1.rho_cd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:29:31.396369+00:00
-- url     : https://prove2.me/submissions/b5d1981b-c98b-4691-a34d-0cd27c60fbc6

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleyForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactlySupportedBanachModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_cdm_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_cdm_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_cd_co

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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.Ux1
theorem _root_.solution (g0 : Mat k r) : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (rho g0) (Sr g0) := by
  have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : Mat k r => x * g0⁻¹) (Sr g0) :=
    cdm_mul contDiffOn_id contDiffOn_const
  have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => iot (x * g0⁻¹)) (Sr g0) := by
    unfold iot
    exact cdm_mul (h1.sub contDiffOn_const) (cdm_inv (h1.add contDiffOn_const) fun x hx => hx)
  exact contDiffOn_pi.2 fun i => cd_co h2 i
end Formalism.FourierDecayAlt.P.Ux1
