-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.biLe_CC_mul_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:14:27.656994+00:00
-- url     : https://prove2.me/submissions/c6b09379-3148-4ffc-b70e-798500746f4b

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_MinorProdBlockDegree
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_biLe_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_biLe_CC
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
private theorem biLe_single_one_X (x : ι) (k : κ) :
    BiLe (Finsupp.single x 1) (MvPolynomial.X k : MvPolynomial κ (MvPolynomial ι K)) := by
  classical
  intro β n hn
  rw [MvPolynomial.coeff_X] at hn
  by_cases hβ : Finsupp.single k 1 = β
  · rw [if_pos hβ] at hn
    obtain rfl := eq_zero_of_mem_support_one hn
    subst hβ
    refine ⟨?_, by simp [Finsupp.degree_single]⟩
    first
      | exact zero_le _
      | exact fun i => Nat.zero_le _
      | simp
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
theorem _root_.solution (x : ι) (a : K) (k : κ) : BiLe (Finsupp.single x 1)
    (MvPolynomial.C (MvPolynomial.C a) * MvPolynomial.X k :
      MvPolynomial κ (MvPolynomial ι K)) := by
  have h := biLe_mul (biLe_CC (ι := ι) (κ := κ) a) (biLe_single_one_X (K := K) x k)
  rwa [zero_add] at h
end Formalism.InvariantFactorPaths.G7
