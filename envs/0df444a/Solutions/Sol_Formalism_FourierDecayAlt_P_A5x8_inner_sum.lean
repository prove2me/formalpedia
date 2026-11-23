-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x8.inner_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:13:25.743848+00:00
-- url     : https://prove2.me/submissions/4de2aeb0-b33b-46f4-96a8-0ade83fd4591

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_comb_identity
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_finsum_of_inj
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_iota_injective
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_tTerm_supp
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_tTerm_iota
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_psiKR_conj
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x3_finite_coker
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x3_finite_dual
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x6_lamLin_out
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x6_psiKR_add
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
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x8
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
namespace Formalism.FourierDecayAlt.P.A5x8
theorem _root_.solution (R : Subring K) (ψ : AddChar K ℂ) (hD : LocalDatum K R ψ) {m m' N N' : ℕ}
    (hN : N = m + 1) (hN' : N' = m' + 1) (Z₁ : Matrix (Fin m) (Fin m) K)
    (Z₂ : Matrix (Fin m') (Fin m') K) (c : Kˣ) (h₁ : IsInt R Z₁) (h₂ : IsInt R Z₂)
    (d₁ : IsUnit Z₁.det) (d₂ : IsUnit Z₂.det) :
    ∑ᶠ y, tTerm R ψ hN hN' Z₁ Z₂ (c : K) y = singleBlockInner R ψ Z₁ Z₂ (c : K) := by
  classical
  have hψ : ∀ r ∈ R, ψ r = 1 := fun r hr => A5x3.psi_of_mem hD.selfDual hr
  have := A5x3.finite_coker hD Z₁ h₁ d₁
  have := A5x3.finite_coker hD Z₂ h₂ d₂
  have : Finite (coker R Z₁ →ₗ[R] KR R) := A5x3.finite_dual hD.selfDual
  have : Finite (coker R Z₂ →ₗ[R] KR R) := A5x3.finite_dual hD.selfDual
  have : Finite (coker R Z₁ ≃ₗ[R] coker R Z₂) :=
    Finite.of_injective (fun θ => (θ : coker R Z₁ → coker R Z₂)) DFunLike.coe_injective
  let := Fintype.ofFinite (coker R Z₁)
  let := Fintype.ofFinite (coker R Z₂)
  let := Fintype.ofFinite (coker R Z₁ →ₗ[R] KR R)
  let := Fintype.ofFinite (coker R Z₂ →ₗ[R] KR R)
  let := Fintype.ofFinite (coker R Z₁ ≃ₗ[R] coker R Z₂)
  rw [finsum_of_inj _ (iota_injective R Z₁ Z₂ h₁ h₂ d₁ d₂) _ (tTerm_supp R ψ hN hN' Z₁ Z₂ _ d₁ d₂),
    finsum_eq_sum_of_fintype,
    Finset.sum_congr rfl fun s _ => tTerm_iota R ψ hψ hN hN' Z₁ Z₂ c h₁ h₂ d₁ d₂ s]
  have hc := comb_identity (Θ := coker R Z₁ ≃ₗ[R] coker R Z₂)
    (P₁ := fun (a : coker R Z₁ →ₗ[R] KR R) (b : coker R Z₁) =>
      a b = -(Submodule.Quotient.mk (c : K) : KR R))
    (P₂ := fun (a : coker R Z₂ →ₗ[R] KR R) (b : coker R Z₂) =>
      a b = -(Submodule.Quotient.mk (c : K) : KR R))
    (ta := fun θ a => a.comp θ.symm.toLinearMap) (tc := fun θ b => θ b)
    (Q := fun θ a b a' b' => (∀ y, a' (θ y) = a y) ∧ θ b = b')
    (by
      intro θ a b a' b'
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h2.symm⟩
        apply LinearMap.ext
        intro y
        simp [← h1]
      · rintro ⟨rfl, rfl⟩
        exact ⟨fun y => by simp, rfl⟩)
    (by intro θ a b; simp)
    (fun a b => psiKR R ψ (a (eZ R Z₁) + A5x6.muZ R Z₁ d₁ b))
    (fun a b => conj (psiKR R ψ (a (eZ R Z₂) + A5x6.muZ R Z₂ d₂ b)))
  refine Eq.trans ?_ (hc.trans ?_)
  · exact Finset.sum_congr rfl fun s _ => rfl
  · unfold singleBlockInner
    rw [finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun θ _ => ?_
    rw [finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hab : a b = -(Submodule.Quotient.mk (c : K) : KR R)
    · rw [if_pos hab, if_pos hab, psiKR_conj R ψ hD, ← A5x6.psiKR_add R ψ hψ,
        A5x6.lamLin_out R Z₁ d₁, A5x6.lamLin_out R Z₂ d₂]
      congr 1
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, map_sub]
      abel
    · rw [if_neg hab, if_neg hab]
end Formalism.FourierDecayAlt.P.A5x8
