-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBG.AAop_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:00:52.703807+00:00
-- url     : https://prove2.me/submissions/712a3417-bb92-4127-b9b6-4050318e528d

import Definitions.Def_Formalism_HermitianCurvature_StatementD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieDecompositionLocal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeadingTermIdentity
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGLet
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBG_qminor_agree
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_pe_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_ps_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.SignAntidiagonal.pe_val
attribute [local simp] Formalism.FourierDecayAlt.P.SignAntidiagonal.ps_val



set_option autoImplicit false
open Matrix Finset
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBG
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Classical
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (U₀ : Set (Mat k r)) (hU₀ : IsOpen U₀)
namespace Formalism.FourierDecayAlt.P.PBG
theorem _root_.solution (m : ℕ) (hm : m ≤ r) (u : ℂ) (f : Wsm (E := E) U₀) (g₀ : Mat k r) (hg : g₀ ∈ U₀)
    (hgG : g₀ ∈ GV k r) :
    C3.AAop k r m hm u f.1 g₀ = ((C3.AAx k r (fun a b => EHt (E := E) U₀ hU₀ a b) (xi0 g₀) m hm u) f).1 g₀ := by
  unfold C3.AAop C3.AAx
  rw [LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro c _
  split_ifs
  · rw [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply, qminor_agree U₀ hU₀ _ _ _ f g₀ hg hgG]
    rfl
  · simp
end Formalism.FourierDecayAlt.P.PBG
