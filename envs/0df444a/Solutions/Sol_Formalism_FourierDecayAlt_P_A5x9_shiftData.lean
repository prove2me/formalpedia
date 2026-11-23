-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x9.shiftData
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:06:42.286547+00:00
-- url     : https://prove2.me/submissions/cb6996fc-3693-4948-8e60-911e3ee52cd7

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_Lam_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_isD_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_isD_mulVec_msk
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_shf_isPP
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_shf_sUp
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_shf_Lam_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_shf_isInt
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_shf_mem
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x2_lamTil_fin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val



set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x9
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ} (k : ℕ)
namespace Formalism.FourierDecayAlt.P.A5x9
theorem _root_.solution (ψ : AddChar K ℂ) (hsd : ∀ a : K, (∀ r ∈ R, ψ (a * r) = 1) ↔ a ∈ R)
    (hk : k + 2 ≤ n) (Z₀ Z₀' : Matrix (Fin n) (Fin n) K) (hd : IsUnit Z₀.det)
    (hd' : IsUnit Z₀'.det) (Ψ : MM R k Z₀ ≃ₗ[R] MM R k Z₀') (hΨ : GB R k Z₀ Z₀' Ψ) :
    ∃ σ σ' : Matrix (Fin n) (Fin n) K, IsPP R k σ ∧ IsPP R k σ' ∧ ψ (sUp σ - sUp σ') ≠ 1 ∧
      ∀ p p' : Matrix (Fin n) (Fin n) K, IsPP R k p → IsPP R k p' → IsInt R (Z₀ * p) →
        IsInt R (Z₀' * p') → Rel R Ψ (latZ R (Z₀ * p)) (latZ R (Z₀' * p')) →
        IsInt R (Z₀ * (σ * p)) ∧ IsInt R (Z₀' * (σ' * p')) ∧
          Rel R Ψ (latZ R (Z₀ * (σ * p))) (latZ R (Z₀' * (σ' * p'))) := by
  obtain ⟨D, _, hL⟩ := hΨ.lift
  obtain ⟨x0, y0, hxy, hx0, hbad⟩ := hΨ.bad
  have hex : ∃ r ∈ R, ψ ((lamTil R Z₀' k y0 - lamTil R Z₀ k x0) * r) ≠ 1 := by
    by_contra hcon
    refine hbad ((hsd _).1 fun r hr => ?_)
    by_contra h
    exact hcon ⟨r, hr, h⟩
  obtain ⟨r0, hr0, hψ⟩ := hex
  let ρ : R := ⟨r0, hr0⟩
  let m : Fin n → R := ρ • x0
  let m' : Fin n → R := ρ • y0
  have hmm : Ψ (Submodule.Quotient.mk m) = Submodule.Quotient.mk m' := by
    simp only [m, m', Submodule.Quotient.mk_smul, map_smul, hxy]
  have hm : abelian₂ R k Z₀ m = 0 := by simp only [m, map_smul, hx0, smul_zero]
  have hm' : abelian₂ R k Z₀' m' = 0 := by rw [hL m m' hmm, hm, Matrix.mulVec_zero]
  let c : Fin n := ⟨k + 1, by omega⟩
  let r : Fin n := ⟨k, by omega⟩
  have hDi := isD_inv R k D.2
  let β : Fin n → K := Pi.single c 1
  let β' : Fin n → K := D.1⁻¹ c
  have hβi : ∀ b, β b ∈ R := by
    intro b
    by_cases h : b = c
    · simp [β, h, R.one_mem]
    · simp [β, h, R.zero_mem]
  have hβ : ∀ b : Fin n, b.val ≤ k → β b = 0 := by
    intro b hb
    have : b ≠ c := by
      intro h
      rw [h] at hb
      simp [c] at hb
    simp [β, this]
  have hβi' : ∀ b, β' b ∈ R := fun b => hDi.2.1 c b
  have hβ' : ∀ b : Fin n, b.val ≤ k → β' b = 0 := by
    intro b hb
    have hbc : b < c := by
      rw [Fin.lt_def]
      simp only [c]
      omega
    exact hDi.1.1 hbc
  have hξ := shf_Lam_zero R k Z₀ m hm
  have hξ' := shf_Lam_zero R k Z₀' m' hm'
  refine ⟨1 + vecMulVec (Z₀⁻¹ *ᵥ coeLin R m) β, 1 + vecMulVec (Z₀'⁻¹ *ᵥ coeLin R m') β',
    shf_isPP R k _ β hξ hβ, shf_isPP R k _ β' hξ' hβ', ?_, ?_⟩
  · rw [shf_sUp k _ β hξ hβ r c rfl rfl, shf_sUp k _ β' hξ' hβ' r c rfl rfl]
    have e1 : β c = 1 := by simp [β]
    have e2 : β' c = 1 := hDi.1.2 c
    rw [e1, e2, mul_one, mul_one, ← A5x2.lamTil_fin R Z₀ r m, ← A5x2.lamTil_fin R Z₀' r m']
    have e3 : lamTil R Z₀ r.val m - lamTil R Z₀' r.val m' =
        -((lamTil R Z₀' k y0 - lamTil R Z₀ k x0) * r0) := by
      simp only [m, m', map_smul, r]
      have hs : ∀ a : K, ρ • a = r0 * a := fun a => rfl
      rw [hs, hs]
      ring
    rw [e3, AddChar.map_neg_eq_inv]
    intro h
    exact hψ (inv_eq_one.1 h)
  · intro p p' hp hp' hZ hZ' hrel
    refine ⟨shf_isInt R k Z₀ p hd hp hZ m β hβi hβ, shf_isInt R k Z₀' p' hd' hp' hZ' m' β' hβi' hβ',
      ?_⟩
    intro x y hxy'
    rw [shf_mem R k Z₀ p hd hp m hm β hβi hβ x, shf_mem R k Z₀' p' hd' hp' m' hm' β' hβi' hβ' y]
    have hρ : β' ⬝ᵥ (Z₀'⁻¹ *ᵥ coeLin R y) = β ⬝ᵥ (Z₀⁻¹ *ᵥ coeLin R x) := by
      have h1 := hL x y hxy'
      have h2 : D.1⁻¹ *ᵥ abelian₂ R k Z₀' y = abelian₂ R k Z₀ x := by
        rw [h1, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _
          (by rw [isUpUni_det K D.2.1]; exact isUnit_one), Matrix.one_mulVec]
      rw [Lam_apply, Lam_apply, isD_mulVec_msk R k hDi] at h2
      have h3 := congrFun h2 c
      have hkc : k < c.val := by simp [c]
      simp only [msk, hkc, if_true] at h3
      have h4 : β ⬝ᵥ (Z₀⁻¹ *ᵥ coeLin R x) = (Z₀⁻¹ *ᵥ coeLin R x) c := by
        simp [β]
      rw [h4, ← h3]
      rfl
    have hsub : ∀ s : R, Ψ (Submodule.Quotient.mk (x - s • m)) =
        Submodule.Quotient.mk (y - s • m') := by
      intro s
      have e1 : (Submodule.Quotient.mk (x - s • m) : MM R k Z₀) =
          Submodule.Quotient.mk x - s • Submodule.Quotient.mk m := rfl
      have e2 : (Submodule.Quotient.mk (y - s • m') : MM R k Z₀') =
          Submodule.Quotient.mk y - s • Submodule.Quotient.mk m' := rfl
      rw [e1, e2, map_sub, map_smul, hxy', hmm]
    constructor
    · rintro ⟨s, hs, hmem⟩
      exact ⟨s, by rw [hρ]; exact hs, (hrel _ _ (hsub s)).1 hmem⟩
    · rintro ⟨s, hs, hmem⟩
      exact ⟨s, by rw [← hρ]; exact hs, (hrel _ _ (hsub s)).2 hmem⟩
end Formalism.FourierDecayAlt.P.A5x9
