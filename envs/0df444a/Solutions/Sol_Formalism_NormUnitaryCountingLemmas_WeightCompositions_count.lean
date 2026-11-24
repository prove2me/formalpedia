-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.WeightCompositions.count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:38:52.009668+00:00
-- url     : https://prove2.me/submissions/75133163-fed3-4471-80e5-6e8371f8eabb

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_ShearCoefficients
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_LtSuccOfMemWeightCompositions
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_WeightCompositions_finrank_eq_sum_components
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_WeightCompositions_mem_S0_of_sum_eq
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_WeightCompositions_sum_eq_of_mem_weightCompositions
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_WeightCompositions_lt_succ_of_mem_weightCompositions
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_WeightCompositions_comp_eq_zero
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_WeightCompositions_finrank_Hw_perm
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_WeightCompositions_finrank_T_inf
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_WeightCompositions_T_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
universe u
open Formalism Formalism.NormUnitaryCountingLemmas
open Formalism.NormUnitaryCountingLemmas.WeightCompositions
variable {N n : ℕ}
variable {K : Type u} [Field K] (ν : Fin N → ℕ)
namespace Formalism.NormUnitaryCountingLemmas.WeightCompositions
theorem _root_.solution (h3p : NormUnitaryPermutationInvariance.{u}) (h3w : NormUnitaryWeight.{u}) (ν : Fin N → ℕ) (k : Fin n) :
    n * ∑ i ∈ Finset.range (∑ j, ν j + 1),
        i * Module.finrank K (H K ν ⊓ weightedHomogeneousSubmodule K (coordKWt N n k) i :
          Submodule K (MvPolynomial (Fin N × Fin n) K)) =
      (∑ j, ν j) * Module.finrank K (H K (n := n) ν) := by
  classical
  set s := ∑ j, ν j with hs

  have hT : ∀ i, Module.finrank K ↥(H K ν ⊓ weightedHomogeneousSubmodule K (coordKWt N n k) i) =
      ∑ w ∈ S0 n s, if w k = i then Dw K ν w else 0 := by
    intro i
    have : FiniteDimensional K ↥(H K ν ⊓ weightedHomogeneousSubmodule K (coordKWt N n k) i) :=
      Submodule.finiteDimensional_of_le inf_le_left
    rw [finrank_eq_sum_components (coordWt N n) _ (S0 n s) (T_comp ν h3w k i)
      (fun F hF w hw => comp_eq_zero ν (Submodule.mem_inf.mp hF).1 w hw)]
    exact Finset.sum_congr rfl fun w _ => finrank_T_inf ν k i w
  have hH : Module.finrank K (H K (n := n) ν) = ∑ w ∈ S0 n s, Dw K ν w :=
    finrank_eq_sum_components (coordWt N n) _ (S0 n s) (fun F hF w => h3w K N n ν F hF w)
      (fun F hF w hw => comp_eq_zero ν hF w hw)
  have hL : ∑ i ∈ Finset.range (s + 1),
      i * Module.finrank K ↥(H K ν ⊓ weightedHomogeneousSubmodule K (coordKWt N n k) i) =
      ∑ w ∈ S0 n s, w k * Dw K ν w := by
    simp only [hT, Finset.mul_sum, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr (lt_succ_of_mem_weightCompositions hw k))]
  have hA : ∀ k', ∑ w ∈ S0 n s, w k' * Dw K ν w = ∑ w ∈ S0 n s, w k * Dw K ν w := by
    intro k'
    let σ := Equiv.swap k k'
    let e : (Fin n → ℕ) ≃ (Fin n → ℕ) :=
      { toFun := fun w => w ∘ σ, invFun := fun w => w ∘ σ.symm,
        left_inv := fun w => by funext x; simp, right_inv := fun w => by funext x; simp }
    apply Finset.sum_equiv e
    · intro w
      constructor
      · intro hw
        apply mem_S0_of_sum_eq
        rw [← sum_eq_of_mem_weightCompositions hw]
        exact Equiv.sum_comp σ w
      · intro hw
        apply mem_S0_of_sum_eq
        rw [← sum_eq_of_mem_weightCompositions hw]
        exact (Equiv.sum_comp σ w).symm
    · intro w _
      show w k' * Dw K ν w = (w ∘ σ) k * Dw K ν (w ∘ σ)
      rw [Function.comp_apply, Equiv.swap_apply_left]
      unfold Dw
      rw [finrank_Hw_perm ν h3p σ w]
  rw [hL]
  calc n * ∑ w ∈ S0 n s, w k * Dw K ν w
      = ∑ k' : Fin n, ∑ w ∈ S0 n s, w k' * Dw K ν w := by
        rw [Finset.sum_congr rfl (fun k' _ => hA k'), Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, smul_eq_mul]
    _ = ∑ w ∈ S0 n s, (∑ k', w k') * Dw K ν w := by
        rw [Finset.sum_comm]
        simp only [Finset.sum_mul]
    _ = ∑ w ∈ S0 n s, s * Dw K ν w :=
        Finset.sum_congr rfl fun w hw => by rw [sum_eq_of_mem_weightCompositions hw]
    _ = s * Module.finrank K (H K (n := n) ν) := by rw [← Finset.mul_sum, hH]
end Formalism.NormUnitaryCountingLemmas.WeightCompositions
