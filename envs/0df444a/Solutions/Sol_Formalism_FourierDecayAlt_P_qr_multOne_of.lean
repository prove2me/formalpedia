-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.qr_multOne_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:55:49.428206+00:00
-- url     : https://prove2.me/submissions/c3db5202-1de5-43d5-8bef-6af77359a6e6

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IntegerProductCast_OfFnProdIntCast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightMonotonicity
import Theorems.Thm_Formalism_FourierDecayAlt_P_DegreeMapArithmetic_weight_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr DegreeMapArithmetic
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution (hS : Qr.ExistsSingMax) (hD : Qr.DualMinor) (hP : Qr.SpanSing) : Qr.MultOne := by
  intro V _ _ _ n E μ w₁ w₂ hE hIrr h1 h2 hw1
  have : Nontrivial V := hIrr.1
  obtain ⟨ν, ξ₀, -, hξ0, hHW, -⟩ := hS (Module.Dual ℂ V) (n + 1) (dualE E) (hD V (n + 1) E hE).1 ⊤
    (fun _ _ _ _ => Submodule.mem_top) top_ne_bot
  have hdiag : ∀ (a : Fin (n + 1)) (v : V), ξ₀ (E a a v) = ν a * ξ₀ v := by
    intro a v
    have := congrArg (fun ζ : Module.Dual ℂ V => ζ v) (hHW.1 a)
    simpa [dualE, LinearMap.dualMap_apply] using this
  have hlow : ∀ a b : Fin (n + 1), b < a → ∀ v, ξ₀ (E a b v) = 0 := by
    intro a b hab v
    have := congrArg (fun ζ : Module.Dual ℂ V => ζ v) (hHW.2 b a hab)
    simpa [dualE, LinearMap.dualMap_apply] using this
  have key : ∀ w, IsHW (subA E) μ w → ∀ a : Fin n → ℕ, ξ₀ (mono (etaK E) a w) ≠ 0 →
      ∀ c, (a c : ℂ) = ν c.castSucc - μ c := by
    intro w hw a ha c
    have e1 := hdiag c.castSucc (mono (etaK E) a w)
    rw [weight_mono E hE c (μ c) w (hw.1 c) a, map_smul, smul_eq_mul] at e1
    have := mul_right_cancel₀ ha e1
    rw [← this]; ring
  have hex : ∃ a₀ : Fin n → ℕ, ξ₀ (mono (etaK E) a₀ w₁) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hw1 (hP V n E ξ₀ μ w₁ hE hIrr hξ0 hlow h1 hcon)
  obtain ⟨a₀, ha₀⟩ := hex
  refine ⟨ξ₀ (mono (etaK E) a₀ w₂) / ξ₀ (mono (etaK E) a₀ w₁), ?_⟩
  set c := ξ₀ (mono (etaK E) a₀ w₂) / ξ₀ (mono (etaK E) a₀ w₁) with hc
  have hw : IsHW (subA E) μ (w₂ - c • w₁) := by
    refine ⟨fun a => ?_, fun a b hab => ?_⟩
    · rw [map_sub, map_smul, h1.1 a, h2.1 a, smul_sub, smul_comm]
    · rw [map_sub, map_smul, h1.2 a b hab, h2.2 a b hab, smul_zero, sub_zero]
  have hz : w₂ - c • w₁ = 0 := by
    refine hP V n E ξ₀ μ _ hE hIrr hξ0 hlow hw (fun a => ?_)
    by_contra hne
    have haa : a = a₀ := by
      funext x
      have e1 := key _ hw a hne x
      have e2 := key _ h1 a₀ ha₀ x
      exact Nat.cast_injective (R := ℂ) (e1.trans e2.symm)
    subst haa
    apply hne
    rw [map_sub, map_sub, map_smul, map_smul, smul_eq_mul, hc, div_mul_cancel₀ _ ha₀, sub_self]
  exact sub_eq_zero.mp hz
end Formalism.FourierDecayAlt.P
