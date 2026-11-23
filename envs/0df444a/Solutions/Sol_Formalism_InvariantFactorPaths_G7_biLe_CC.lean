-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.biLe_CC
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:01:53.294811+00:00
-- url     : https://prove2.me/submissions/2654f780-fb86-4557-b593-ece089580fc6

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
private theorem eq_zero_of_mem_support_C {R σ : Type*} [CommSemiring R] {a : R} {n : σ →₀ ℕ}
    (hn : n ∈ (MvPolynomial.C a : MvPolynomial σ R).support) : n = 0 := by
  classical
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C] at hn
  by_contra h
  exact hn (if_neg (Ne.symm h))
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
theorem _root_.solution (a : K) :
    BiLe 0 (MvPolynomial.C (MvPolynomial.C a) : MvPolynomial κ (MvPolynomial ι K)) := by
  intro β n hn
  obtain ⟨hβ, hn'⟩ := eq_zero_and_mem_support_of_mem_support_coeff_C hn
  obtain rfl := eq_zero_of_mem_support_C hn'
  subst hβ
  exact ⟨le_rfl, by simp⟩
end Formalism.InvariantFactorPaths.G7
