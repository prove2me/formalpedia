-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBG.qminor_agree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:51:34.749209+00:00
-- url     : https://prove2.me/submissions/045af57c-2c3b-4a94-ae5c-120f9cbf0c45

import Definitions.Def_Formalism_HermitianCurvature_StatementD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieDecompositionLocal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeadingTermIdentity
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGLet
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBG_top_agree
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_PBG_top_congr__5b36e678b711
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBG_fold_agree
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
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
theorem _root_.solution {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ) (f : Wsm (E := E) U₀) (g : Mat k r)
    (hg : g ∈ U₀) (hgG : g ∈ GV k r) :
    ((qminor (fun a b => EHt (E := E) U₀ hU₀ a b) a b u) f).1 g = qminorOp (EabH (Hpk k r)) a b u f.1 g := by
  unfold qminor qminorOp
  rw [LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Module.End.mul_apply]
  have hL := fold_agree U₀ (List.ofFn fun i : Fin t =>
      (Tm (fun a b => EHt (E := E) U₀ hU₀ a b) (u - ((i : ℕ) : ℂ)) (a (σ i)) (b i),
        QuantumDeterminants.Top (EabH (Hpk k r)) (u - ((i : ℕ) : ℂ)) (a (σ i)) (b i)))
    (by
      intro p hp h x hx hxG
      obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hp
      exact top_agree U₀ hU₀ _ _ _ h x hx hxG)
    (by
      intro p hp h₁ h₂ he x hx hxG
      obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hp
      exact top_congr' U₀ hU₀ _ _ _ he x hx hxG)
    f g hg hgG
  rw [List.map_ofFn, List.map_ofFn] at hL
  simp only [Function.comp_def] at hL
  rw [Pi.smul_apply]
  have hz : ∀ (z : ℤ) (v : Wsm (E := E) U₀), ((z : Module.End ℂ (Wsm (E := E) U₀)) v) = (z : ℂ) • v := by
    intro z v
    rw [Module.End.intCast_apply, Int.cast_smul_eq_zsmul]
  rw [hz, Submodule.coe_smul, Pi.smul_apply, hL]
end Formalism.FourierDecayAlt.P.PBG
