-- Prove2me | solution 1 for FD1D.expected_haarL2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:32:30.045684+00:00
-- url     : https://prove2.me/submissions/1a75ce10-db30-4d73-9de7-af989691e5e0

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
import Theorems.Thm_FD1D_dyadicTent_sq_integral
import Theorems.Thm_FD1D_dyadicTent_mul_eq_zero_of_separated
import Theorems.Thm_FD1D_FiniteLaw_expect_eq_zero_of_oddSymmetry
import Theorems.Thm_FD1D_haarL2_eq_gram
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.FiniteLaw.expect_const


section
namespace FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
namespace DyadicMass
end DyadicMass
namespace HaarTerm
end HaarTerm
namespace DyadicMass
end DyadicMass
namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]
end FiniteLaw
variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]
namespace DyadicMass
end DyadicMass
private theorem expect_double_sum (μ : FiniteLaw Ω) (b : Ω → ι → ℝ)
    (G : ι → ι → ℝ) :
    μ.expect (fun ω => ∑ i, ∑ j, (b ω i * b ω j) * G i j) =
      ∑ i, ∑ j, G i j * μ.expect (fun ω => b ω i * b ω j) := by
  rw [FiniteLaw.expect]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [FiniteLaw.expect, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  ring
namespace MonotoneQuantilePolicy
end MonotoneQuantilePolicy
namespace FiniteLaw
end FiniteLaw
end
end FD1D
end

set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]
namespace FD1D
theorem _root_.solution (μ : FiniteLaw Ω) (l p : ι → ℝ)
    (b : Ω → ι → ℝ) (hp : ∀ i, 0 < p i)
    (hsym : ∀ i j, i ≠ j → IntervalsSeparated l p i j ∨
      μ.OddSymmetry (fun ω => b ω i * b ω j)) :
    μ.expect (fun ω => haarL2 l p (b ω)) =
      (1 / 12) * ∑ i, p i * μ.expect (fun ω => (b ω i) ^ 2) := by
  simp_rw [haarL2_eq_gram l p _ hp]
  rw [expect_double_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · rw [show (fun ω => b ω i * b ω i) = fun ω => (b ω i) ^ 2 by
      funext
      ring]
    rw [show (fun z => dyadicTent (l i) (p i) z * dyadicTent (l i) (p i) z) =
      fun z => dyadicTent (l i) (p i) z ^ 2 by
      funext
      ring]
    rw [dyadicTent_sq_integral _ _ (hp i)]
    ring
  · intro j _ hji
    have hij : i ≠ j := Ne.symm hji
    rcases hsym i j hij with hsep | hodd
    · have hzero : (fun z => dyadicTent (l i) (p i) z *
          dyadicTent (l j) (p j) z) = fun _ => 0 := by
        funext z
        exact dyadicTent_mul_eq_zero_of_separated (hp i) (hp j) hsep
      rw [hzero]
      simp
    · rw [μ.expect_eq_zero_of_oddSymmetry _ hodd]
      simp
  · simp
end FD1D
