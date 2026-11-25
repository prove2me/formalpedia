-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBG.poly_AAvop
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:39:08.016011+00:00
-- url     : https://prove2.me/submissions/95e0a1ea-e2a9-45af-9ccc-e5475a6fd395

import Definitions.Def_Formalism_HermitianCurvature_StatementD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieDecompositionLocal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeadingTermIdentity
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGLet
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBG_AAvop_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_leading_term_vector_identity
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
include hU₀
namespace Formalism.FourierDecayAlt.P.PBG
theorem _root_.solution (m : ℕ) (hm : m ≤ r) (f : Wsm (E := E) U₀) (g₀ : Mat k r) (hg : g₀ ∈ U₀)
    (hgG : g₀ ∈ GV k r) :
    PolyRepN m (fun ell => C3.AAvop k r m hm ell f.1 g₀)
      ((Matrix.of fun a b : Fin m => y0 g₀ (Fin.castLE hm a) (C3.sR k r m hm b)).det • f.1 g₀) := by
  obtain ⟨B, hB⟩ := Formalism.FourierDecayAlt.P.SignAntidiagonal.leading_term_vector_identity (Module.End ℂ (Wsm (E := E) U₀)) k r
    (fun a b => EHt (E := E) U₀ hU₀ a b) (y0 g₀) m hm
  refine ⟨fun l => if h : l < m then (B ⟨l, h⟩ f).1 g₀ else
    (Matrix.of fun a b : Fin m => y0 g₀ (Fin.castLE hm a) (C3.sR k r m hm b)).det • f.1 g₀, by simp, fun u => ?_⟩
  beta_reduce
  rw [AAvop_eq U₀ hU₀ m hm u f g₀ hg hgG, hB u, Finset.sum_range_succ, dif_neg (lt_irrefl m)]
  simp only [LinearMap.add_apply, Module.algebraMap_end_apply, LinearMap.sum_apply, Module.End.mul_apply,
    Submodule.coe_add, Submodule.coe_smul, Submodule.coe_sum, Pi.add_apply, Pi.smul_apply, Finset.sum_apply]
  rw [add_comm, Finset.sum_range (fun l => u ^ l • if h : l < m then (B ⟨l, h⟩ f).1 g₀ else _)]
  congr 1
  · apply Finset.sum_congr rfl
    intro l _
    rw [dif_pos l.isLt]
  · rw [smul_smul]
end Formalism.FourierDecayAlt.P.PBG
