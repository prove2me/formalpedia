-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x6.extend_to_orthogonal_basis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:14:14.857605+00:00
-- url     : https://prove2.me/submissions/76048303-1d40-40a7-8327-1a83bcdf8c98

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictOrthogonalComplementNondeg
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_exists_orthonormal
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_form_sum_right_alt
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_gram_mulVec_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_form_functionals_surjective
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_linearIndependent_of_gram_unit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x6
open Module
variable {K : Type} [Field K] {σ : K →+* K}
variable {V : Type} [AddCommGroup V] [Module K V]
namespace Formalism.FourierDecayAlt.P.S3x6
theorem _root_.solution (hσ : Inv σ) [FiniteDimensional K V] (h : V →ₛₗ[σ] V →ₗ[K] K) (hh : Herm h)
    (hn : Nondeg h) {a : ℕ} (x : Fin a → V) (hG : IsUnit (gramMatrix h x).det) :
    ∃ b : Basis (Fin a ⊕ Fin (finrank K V - a)) K V, (∀ i, b (Sum.inl i) = x i) ∧
      (∀ i j, h (b (Sum.inl i)) (b (Sum.inr j)) = 0) ∧
      (∀ i j, h (b (Sum.inr j)) (b (Sum.inl i)) = 0) ∧
      ∀ j k, h (b (Sum.inr j)) (b (Sum.inr k)) = if j = k then 1 else 0 := by
  have hx : LinearIndependent K x := linearIndependent_of_gram_unit h x hG
  let Φ : V →ₗ[K] (Fin a → K) := LinearMap.pi (fun i => h (x i))
  have hΦ : ∀ v i, Φ v i = h (x i) v := fun v i => rfl
  have hsurj : LinearMap.range Φ = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro r
    obtain ⟨m, hm⟩ := form_functionals_surjective hσ h hn x hx r
    exact ⟨m, funext hm⟩
  let W : Submodule K V := LinearMap.ker Φ
  have hWmem : ∀ w, w ∈ W ↔ ∀ i, h (x i) w = 0 := by
    intro w
    simp only [W, LinearMap.mem_ker]
    constructor
    · intro hw i
      rw [← hΦ, hw]; rfl
    · intro hw
      funext i
      exact hw i
  have hfr : finrank K W = finrank K V - a := by
    have h1 : finrank K (LinearMap.range Φ) + finrank K W = finrank K V :=
      LinearMap.finrank_range_add_finrank_ker Φ
    rw [hsurj, finrank_top, Module.finrank_fin_fun] at h1
    omega
  have hdec : ∀ v, ∃ c : Fin a → K, v - ∑ j, c j • x j ∈ W := by
    intro v
    refine ⟨(gramMatrix h x)⁻¹.mulVec (Φ v), ?_⟩
    rw [hWmem]
    intro i
    rw [map_sub, ← gram_mulVec_eq, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hG,
      Matrix.one_mulVec, hΦ, sub_self]
  let hW : W →ₛₗ[σ] W →ₗ[K] K := h.domRestrict₁₂ W W
  have hWh : Herm hW := fun u v => hh u v
  have hWn : Nondeg hW := by
    intro w hw
    apply Subtype.ext
    apply hn
    intro v
    obtain ⟨c, hc⟩ := hdec v
    have h1 : h w (v - ∑ j, c j • x j) = 0 := hw ⟨_, hc⟩
    have h2 : h w (∑ j, c j • x j) = 0 := by
      rw [form_sum_right_alt]
      refine Finset.sum_eq_zero (fun j _ => ?_)
      rw [← hh (x j) w, (hWmem w).1 w.2 j]
      simp
    rw [map_sub, h2, sub_zero] at h1
    exact h1
  obtain ⟨c, hc⟩ := exists_orthonormal hσ _ W hW hWh hWn hfr
  let z : Fin a ⊕ Fin (finrank K V - a) → V := Sum.elim x (fun j => (c j : V))
  have h12 : ∀ i j, h (x i) (c j : V) = 0 := fun i j => (hWmem _).1 (c j).2 i
  have h21 : ∀ i j, h (c j : V) (x i) = 0 := by
    intro i j
    rw [← hh, h12]; simp
  have h22 : ∀ j k, h (c j : V) (c k : V) = if j = k then 1 else 0 := fun j k => hc j k
  have hzG : gramMatrix h z = Matrix.fromBlocks (gramMatrix h x) 0 0 1 := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · rfl
    · simp [gramMatrix, z, h12]
    · simp [gramMatrix, z, h21]
    · simp [gramMatrix, z, h22, Matrix.one_apply]
  have hzli : LinearIndependent K z := by
    apply linearIndependent_of_gram_unit h
    rw [hzG, Matrix.det_fromBlocks_zero₂₁]
    simpa using hG
  have hcard : Fintype.card (Fin a ⊕ Fin (finrank K V - a)) = finrank K V := by
    have h1 := hx.fintype_card_le_finrank
    simp only [Fintype.card_fin] at h1
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  have hsp := hzli.span_eq_top_of_card_eq_finrank' hcard
  refine ⟨Basis.mk hzli hsp.ge, ?_, ?_, ?_, ?_⟩
  · intro i; simp [z]
  · intro i j; simp [z, h12]
  · intro i j; simp [z, h21]
  · intro j k; simp [z, h22]
end Formalism.FourierDecayAlt.P.S3x6
