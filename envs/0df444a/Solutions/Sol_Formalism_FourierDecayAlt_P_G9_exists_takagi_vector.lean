-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G9.exists_takagi_vector
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:05:09.681558+00:00
-- url     : https://prove2.me/submissions/1d3a02a3-78cf-41b1-8cdc-07c49425710f

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace ComplexConjugate
open Module
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G9
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
namespace Formalism.FourierDecayAlt.P.G9
theorem _root_.solution (T : E →ₗ⋆[ℂ] E) (hT : ∀ x y, ⟪T x, y⟫_ℂ = ⟪T y, x⟫_ℂ)
    (S : Submodule ℂ E) (hS : ∀ x ∈ S, T x ∈ S) (hne : S ≠ ⊥) :
    ∃ v ∈ S, ∃ σ : ℝ, 0 ≤ σ ∧ ‖v‖ = 1 ∧ T v = (σ : ℂ) • v := by
  let A : E →ₗ[ℂ] E := T.comp T
  have hA : ∀ x ∈ S, A x ∈ S := fun x hx => hS _ (hS _ hx)
  have : Nontrivial S := Submodule.nontrivial_iff_ne_bot.2 hne
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (A.restrict hA)
  obtain ⟨x, hx⟩ := hμ.exists_hasEigenvector
  have hx0 : (x : E) ≠ 0 := by simpa using hx.2
  have hAx : T (T x) = μ • (x : E) := by
    have h := congrArg Subtype.val hx.apply_eq_smul
    simpa [A] using h
  have hnx : 0 < ‖(x : E)‖ := norm_pos_iff.2 hx0
  have h1 : conj μ * ((‖(x:E)‖ : ℂ) ^ 2) = ((‖T x‖ : ℂ) ^ 2) := by
    have h : ⟪T (T x), (x:E)⟫_ℂ = ⟪T x, T x⟫_ℂ := hT _ _
    rw [hAx, inner_smul_left, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
    simpa using h
  set σ : ℝ := ‖T x‖ / ‖(x:E)‖ with hσ
  have hσ0 : 0 ≤ σ := by positivity
  have hμσ : μ = (σ : ℂ) ^ 2 := by
    have hxc : ((‖(x:E)‖ : ℂ)) ≠ 0 := by exact_mod_cast hnx.ne'
    have h2 : conj μ = (σ : ℂ) ^ 2 := by
      rw [hσ]; push_cast; field_simp; exact h1
    have h3 := congrArg conj h2
    simpa using h3
  have key : ∀ w ∈ S, w ≠ 0 → T w = (σ : ℂ) • w →
      ∃ v ∈ S, ∃ σ : ℝ, 0 ≤ σ ∧ ‖v‖ = 1 ∧ T v = (σ : ℂ) • v := by
    intro w hw hw0 hTw
    refine ⟨((‖w‖⁻¹ : ℝ) : ℂ) • w, S.smul_mem _ hw, σ, hσ0, ?_, ?_⟩
    · rw [norm_smul, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hw0)]
    · rw [T.map_smulₛₗ, hTw, Complex.conj_ofReal, smul_comm]
  by_cases hy : T x + (σ : ℂ) • (x : E) = 0
  · refine key (Complex.I • (x : E)) (S.smul_mem _ x.2) (smul_ne_zero Complex.I_ne_zero hx0) ?_
    have hTx : T x = -((σ : ℂ) • (x : E)) := eq_neg_of_add_eq_zero_left hy
    rw [T.map_smulₛₗ, hTx, Complex.conj_I, smul_neg, neg_smul, neg_neg, smul_comm]
  · refine key _ (S.add_mem (hS _ x.2) (S.smul_mem _ x.2)) hy ?_
    rw [map_add, T.map_smulₛₗ, hAx, hμσ, Complex.conj_ofReal, smul_add, smul_smul, pow_two, add_comm]
end Formalism.FourierDecayAlt.P.G9
