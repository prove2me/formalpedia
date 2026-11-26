-- Prove2me | solution 1 for FD1D.haarCombination_sq_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:32:05.398322+00:00
-- url     : https://prove2.me/submissions/12306c93-6315-44bd-8d75-2f6a5ee1b2f9

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
import Theorems.Thm_FD1D_dyadicTent_mul_integrable
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.FiniteLaw.expect_const



set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]
namespace FD1D
theorem _root_.solution (l p b : ι → ℝ) (hp : ∀ i, 0 < p i) :
    Integrable (fun z => haarCombination l p b z ^ 2) := by
  rw [show (fun z : ℝ => haarCombination l p b z ^ 2) =
      fun z => ∑ i, ∑ j, (b i * b j) *
        (dyadicTent (l i) (p i) z * dyadicTent (l j) (p j) z) by
    funext z
    unfold haarCombination
    simp only [pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring]
  exact integrable_finsetSum _ fun i _ =>
    integrable_finsetSum _ fun j _ =>
      (dyadicTent_mul_integrable _ _ _ _ (hp i)).const_mul _
end FD1D
