-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x6.first_kernel_inner_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:51:56.159358+00:00
-- url     : https://prove2.me/submissions/9cdc441b-9cef-46fe-9dee-d92d0b9701d2

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x6_psiKR_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x6_lamLin_out
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x6_mem_isoZZ_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x6_finsum_fiber
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
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
set_option maxHeartbeats 400000
noncomputable section
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A5x6
namespace Formalism.FourierDecayAlt.P.A5x6
theorem _root_.solution {K : Type} [CommRing K] (R : Subring K) (ψ : AddChar K ℂ)
    (hψ : ∀ r ∈ R, ψ r = 1) {n n' : ℕ} (Z : Matrix (Fin n) (Fin n) K)
    (Z' : Matrix (Fin n') (Fin n') K) (hZ : IsUnit Z.det) (hZ' : IsUnit Z'.det)
    (hC : Finite (coker R Z)) (hC' : Finite (coker R Z')) (hD : Finite (coker R Z →ₗ[R] KR R))
    (hOD1 : ∀ x : coker R Z, x = 0 →
      ∑ᶠ α : coker R Z →ₗ[R] KR R, psiKR R ψ (α x) = (Nat.card (coker R Z) : ℂ))
    (hOD2 : ∀ x : coker R Z, x ≠ 0 → ∑ᶠ α : coker R Z →ₗ[R] KR R, psiKR R ψ (α x) = 0)
    (hO1 : ∀ μ : coker R Z →ₗ[R] KR R, μ = 0 →
      ∑ᶠ β : coker R Z, psiKR R ψ (μ β) = (Nat.card (coker R Z) : ℂ))
    (hO2 : ∀ μ : coker R Z →ₗ[R] KR R, μ ≠ 0 → ∑ᶠ β : coker R Z, psiKR R ψ (μ β) = 0)
    {X : Type} (κ : X → K)
    (hκ : Function.Bijective (fun x => (Submodule.Quotient.mk (κ x) : KR R))) :
    (Function.support fun x => singleBlockInner R ψ Z Z' (κ x)).Finite ∧
      ∑ᶠ x, singleBlockInner R ψ Z Z' (κ x) = (Nat.card (coker R Z) : ℂ) * (Nat.card (coker R Z') : ℂ) *
        (Nat.card (isoZZ R Z Z') : ℂ) := by
  classical
  have : Finite (coker R Z ≃ₗ[R] coker R Z') :=
    Finite.of_injective (fun θ : coker R Z ≃ₗ[R] coker R Z' => (θ : coker R Z → coker R Z'))
      (fun x y h => LinearEquiv.ext (congrFun h))
  let _ := Fintype.ofFinite (coker R Z ≃ₗ[R] coker R Z')
  let _ := Fintype.ofFinite (coker R Z →ₗ[R] KR R)
  let _ := Fintype.ofFinite (coker R Z)
  let f : (coker R Z ≃ₗ[R] coker R Z') × (coker R Z →ₗ[R] KR R) × coker R Z → ℂ := fun τ =>
    psiKR R ψ (τ.2.1 (eZ R Z - τ.1.symm (eZ R Z')) +
      (lamLin R Z (Quotient.out τ.2.2) - lamLin R Z' (Quotient.out (τ.1 τ.2.2))))
  let g : (coker R Z ≃ₗ[R] coker R Z') × (coker R Z →ₗ[R] KR R) × coker R Z → KR R :=
    fun τ => τ.2.1 τ.2.2
  have hform : ∀ c : K, singleBlockInner R ψ Z Z' c =
      ∑ τ, if g τ = -(Submodule.Quotient.mk c : KR R) then f τ else 0 := by
    intro c
    unfold singleBlockInner
    rw [finsum_eq_sum_of_fintype, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro θ _
    rw [finsum_eq_sum_of_fintype, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro α _
    rw [finsum_eq_sum_of_fintype]
  have key := finsum_fiber (fun x => (Submodule.Quotient.mk (κ x) : KR R)) hκ g f
  simp only [hform]
  refine ⟨key.1, ?_⟩
  rw [key.2]
  have hf : ∀ τ, f τ = psiKR R ψ (τ.2.1 (eZ R Z - τ.1.symm (eZ R Z'))) *
      psiKR R ψ ((muZ R Z hZ - (muZ R Z' hZ').comp τ.1.toLinearMap) τ.2.2) := by
    intro τ
    simp only [f]
    rw [psiKR_add R ψ hψ, lamLin_out R Z hZ, lamLin_out R Z' hZ']
    rfl
  simp only [hf]
  rw [Fintype.sum_prod_type]
  have hθ : ∀ θ : coker R Z ≃ₗ[R] coker R Z',
      ∑ y : (coker R Z →ₗ[R] KR R) × coker R Z,
        psiKR R ψ (y.1 (eZ R Z - θ.symm (eZ R Z'))) *
          psiKR R ψ ((muZ R Z hZ - (muZ R Z' hZ').comp θ.toLinearMap) y.2) =
      if θ ∈ isoZZ R Z Z' then (Nat.card (coker R Z) : ℂ) * (Nat.card (coker R Z') : ℂ) else 0 := by
    intro θ
    rw [Fintype.sum_prod_type]
    simp only
    rw [← Finset.sum_mul_sum, ← finsum_eq_sum_of_fintype, ← finsum_eq_sum_of_fintype]
    by_cases h1 : eZ R Z - θ.symm (eZ R Z') = 0
    · by_cases h2 : muZ R Z hZ - (muZ R Z' hZ').comp θ.toLinearMap = 0
      · rw [hOD1 _ h1, hO1 _ h2, if_pos ((mem_isoZZ_iff R Z Z' hZ hZ' θ).mpr ⟨h1, h2⟩),
          ← Nat.card_congr θ.toEquiv]
      · rw [hO2 _ h2, mul_zero, if_neg]
        intro h; exact h2 ((mem_isoZZ_iff R Z Z' hZ hZ' θ).mp h).2
    · rw [hOD2 _ h1, zero_mul, if_neg]
      intro h; exact h1 ((mem_isoZZ_iff R Z Z' hZ hZ' θ).mp h).1
  rw [Finset.sum_congr rfl (fun θ _ => hθ θ), Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul,
    Nat.subtype_card (Finset.univ.filter (· ∈ isoZZ R Z Z')) (by simp)]
  ring
end Formalism.FourierDecayAlt.P.A5x6
