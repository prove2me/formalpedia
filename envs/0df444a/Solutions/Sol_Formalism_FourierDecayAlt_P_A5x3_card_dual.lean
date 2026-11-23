-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x3.card_dual
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:57:15.406075+00:00
-- url     : https://prove2.me/submissions/19d542ed-d698-4f41-846b-67fb87d970a9

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x3_finite_dual
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x3_sum_over_C
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_A5x3_sum_over_dual__ff440f43ee65

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
    (hsep : ∀ c : C, (∀ α : C →ₗ[R] KR R, α c = 0) → c = 0) :
    Nat.card (C →ₗ[R] KR R) = Nat.card C := by
  classical
  have := finite_dual (C := C) h
  have := Fintype.ofFinite C
  have := Fintype.ofFinite (C →ₗ[R] KR R)
  have e1 : ∑ c : C, ∑ α : C →ₗ[R] KR R, psiKR R ψ (α c) = (Nat.card (C →ₗ[R] KR R) : ℂ) := by
    simp_rw [← finsum_eq_sum_of_fintype (fun α : C →ₗ[R] KR R => psiKR R ψ (α _)),
      sum_over_dual' h hsep]
    rw [Finset.sum_ite_eq' Finset.univ (0 : C), if_pos (Finset.mem_univ _)]
  have e2 : ∑ c : C, ∑ α : C →ₗ[R] KR R, psiKR R ψ (α c) = (Nat.card C : ℂ) := by
    rw [Finset.sum_comm]
    have h5 : ∀ α : C →ₗ[R] KR R, ∑ c : C, psiKR R ψ (α c) =
        if α = 0 then (Nat.card C : ℂ) else 0 := by
      intro α
      rw [← finsum_eq_sum_of_fintype, sum_over_C h]
      split_ifs <;> rfl
    simp_rw [h5]
    rw [Finset.sum_ite_eq' Finset.univ (0 : C →ₗ[R] KR R), if_pos (Finset.mem_univ _)]
  exact_mod_cast e1.symm.trans e2
end Formalism.FourierDecayAlt.P.A5x3
