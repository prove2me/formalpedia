-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.biLe_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:57:23.62868+00:00
-- url     : https://prove2.me/submissions/fe33a8d8-d202-46fc-a997-1de8defff8dc

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_MinorProdBlockDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
open Finset
namespace Formalism.InvariantFactorPaths.G7
section BiLe
variable {K ι κ : Type} [Field K]
private theorem eq_zero_of_mem_support_one {R σ : Type*} [CommSemiring R] {n : σ →₀ ℕ}
    (hn : n ∈ (1 : MvPolynomial σ R).support) : n = 0 := by
  classical
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one] at hn
  by_contra h
  exact hn (if_neg (Ne.symm h))
private theorem eq_zero_and_mem_support_of_mem_support_coeff_C {R σ κ' : Type*} [CommSemiring R] {P : MvPolynomial σ R}
    {β : κ' →₀ ℕ} {n : σ →₀ ℕ}
    (hn : n ∈ (MvPolynomial.coeff β (MvPolynomial.C P : MvPolynomial κ' (MvPolynomial σ R))).support) :
    β = 0 ∧ n ∈ P.support := by
  classical
  rw [MvPolynomial.coeff_C] at hn
  by_cases hβ : (0 : κ' →₀ ℕ) = β
  · rw [if_pos hβ] at hn
    exact ⟨hβ.symm, hn⟩
  · rw [if_neg hβ] at hn
    simp at hn
end BiLe
section PosDeg
variable {K σ : Type} [Field K] [DecidableEq σ] {r0 r1 : ℕ}
end PosDeg
end Formalism.InvariantFactorPaths.G7
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
variable {K ι κ : Type} [Field K]
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution : BiLe 0 (1 : MvPolynomial κ (MvPolynomial ι K)) := by
  intro β n hn
  obtain ⟨hβ, hn'⟩ := eq_zero_and_mem_support_of_mem_support_coeff_C (P := (1 : MvPolynomial ι K)) (β := β) (n := n)
    (by rw [MvPolynomial.C_1]; exact hn)
  obtain rfl := eq_zero_of_mem_support_one hn'
  subst hβ
  exact ⟨le_rfl, by simp⟩
end Formalism.InvariantFactorPaths.G7
