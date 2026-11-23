-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x3.mem_of_kills
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:54:04.541982+00:00
-- url     : https://prove2.me/submissions/5d8272f1-447d-400c-b392-25d442a098c9

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x3_finite_dual
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x3_sum_over_C
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x3_sum_over_S
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x3_psiKR_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x3
variable {K : Type} [CommRing K] {R : Subring K} {ψ : AddChar K ℂ}
variable {C : Type} [AddCommGroup C] [Module R C]
namespace Formalism.FourierDecayAlt.P.A5x3
theorem _root_.solution (h : ∀ a : K, (∀ r ∈ R, ψ (a * r) = 1) ↔ a ∈ R) [Finite C]
    (S : Submodule R (C →ₗ[R] KR R)) (μ : C →ₗ[R] KR R)
    (hμ : ∀ c, (∀ α ∈ S, α c = 0) → μ c = 0) : μ ∈ S := by
  classical
  have := finite_dual (C := C) h
  have := Fintype.ofFinite C
  have := Fintype.ofFinite S
  by_contra hn
  have e1 : ∑ c : C, ∑ α : S, psiKR R ψ (((α : C →ₗ[R] KR R) - μ) c) = 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro α _
    rw [← finsum_eq_sum_of_fintype, sum_over_C h, if_neg]
    intro h0
    apply hn
    rw [← sub_eq_zero.1 h0]
    exact α.2
  have e2 : ∀ c : C, ∑ α : S, psiKR R ψ (((α : C →ₗ[R] KR R) - μ) c) =
      if ∀ α ∈ S, α c = 0 then (Nat.card S : ℂ) else 0 := by
    intro c
    have h3 : ∀ α : S, psiKR R ψ (((α : C →ₗ[R] KR R) - μ) c) =
        psiKR R ψ ((α : C →ₗ[R] KR R) c) * psiKR R ψ (-(μ c)) := by
      intro α
      rw [LinearMap.sub_apply, sub_eq_add_neg]
      exact (psiBar h).map_add_eq_mul _ _
    simp_rw [h3]
    rw [← Finset.sum_mul, ← finsum_eq_sum_of_fintype, sum_over_S h]
    split_ifs with hc
    · rw [hμ c hc, neg_zero, psiKR_zero h, mul_one]
    · rw [zero_mul]
  simp_rw [e2] at e1
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul] at e1
  rcases mul_eq_zero.1 e1 with h1 | h1
  · have h4 : (0 : C) ∈ Finset.univ.filter (fun c : C => ∀ α ∈ S, α c = 0) := by
      simp
    rw [Nat.cast_eq_zero, Finset.card_eq_zero] at h1
    rw [h1] at h4
    exact absurd h4 (Finset.notMem_empty _)
  · rw [Nat.cast_eq_zero] at h1
    exact Nat.card_pos.ne' h1
end Formalism.FourierDecayAlt.P.A5x3
