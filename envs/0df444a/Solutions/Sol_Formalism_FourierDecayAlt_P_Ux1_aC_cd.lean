-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux1.aC_cd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:04:46.683096+00:00
-- url     : https://prove2.me/submissions/0da1d0b5-323a-43f6-95b4-5e51f6b3194d

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleyForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactlySupportedBanachModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_cdm_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_cdm_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_cd_co
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_dom_open
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_chart_cd
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_chart_mem
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_isUnit_of_uh


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
theorem _root_.solution {g0 : Mat k r} (hg0 : g0 ∈ GV k r) (i : J k r) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (aC g0 i) (Dom k r) := by
  have h1 : ∀ b, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun Y => fderiv ℝ (chart g0) Y (ebv b)) (Dom k r) :=
    fun b => ((chart_cd g0).fderiv_of_isOpen dom_open (by simp)).clm_apply contDiffOn_const
  have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun Y => (chart g0 Y)⁻¹) (Dom k r) :=
    cdm_inv (chart_cd g0) fun Y hY => Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh (chart_mem hg0 hY)
  have h3 : ∀ b, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (sC g0 i b) (Dom k r) := by
    intro b
    unfold sC kc
    exact (cd_co (cdm_mul (h1 b).neg h2) i).mul contDiffOn_const
  unfold aC
  exact ContDiffOn.sum fun b _ => (h3 b).smul contDiffOn_const
end Formalism.FourierDecayAlt.P.Ux1
