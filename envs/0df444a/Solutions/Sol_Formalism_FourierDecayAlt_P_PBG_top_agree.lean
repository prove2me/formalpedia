-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBG.top_agree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:23:36.094077+00:00
-- url     : https://prove2.me/submissions/ca5e745c-02d3-42fe-93b2-e05935ac6d92

import Definitions.Def_Formalism_HermitianCurvature_StatementD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieDecompositionLocal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeadingTermIdentity
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGLet
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr
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
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (U₀ : Set (Mat k r)) (hU₀ : IsOpen U₀)
namespace Formalism.FourierDecayAlt.P.PBG
theorem _root_.solution (u : ℂ) (a b : Fin (2 * r + k + 1)) (h : Wsm (E := E) U₀) (g : Mat k r) (hg : g ∈ U₀)
    (hgG : g ∈ GV k r) :
    ((Tm (fun a b => EHt (E := E) U₀ hU₀ a b) u a b) h).1 g = QuantumDeterminants.Top (EabH (Hpk k r)) u a b h.1 g := by
  unfold Tm QuantumDeterminants.Top
  simp only [LinearMap.add_apply, Submodule.coe_add, Pi.add_apply]
  congr 1
  · split_ifs
    · simp [Module.algebraMap_end_apply]
    · simp
  · show (if g ∈ U₀ ∧ g ∈ GV k r then _ else _) = _
    rw [if_pos ⟨hg, hgG⟩]
end Formalism.FourierDecayAlt.P.PBG
