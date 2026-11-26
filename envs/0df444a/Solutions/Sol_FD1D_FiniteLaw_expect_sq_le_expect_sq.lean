-- Prove2me | solution 1 for FD1D.FiniteLaw.expect_sq_le_expect_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:33:06.673751+00:00
-- url     : https://prove2.me/submissions/817dc8a1-9dcb-4a25-938c-615c0ecfa41f

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport

set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]
open FD1D.FiniteLaw
namespace FD1D.FiniteLaw
theorem _root_.solution (μ : FiniteLaw Ω) (f : Ω → ℝ) :
    μ.expect f ^ 2 ≤ μ.expect (fun ω => f ω ^ 2) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun ω => Real.sqrt (μ.mass ω))
    (fun ω => Real.sqrt (μ.mass ω) * f ω)
  have hleft : (∑ ω, Real.sqrt (μ.mass ω) *
      (Real.sqrt (μ.mass ω) * f ω)) = μ.expect f := by
    rw [expect]
    apply Finset.sum_congr rfl
    intro ω _
    rw [← mul_assoc, Real.mul_self_sqrt (μ.mass_nonneg ω)]
  have hmass : (∑ ω, Real.sqrt (μ.mass ω) ^ 2) = 1 := by
    calc
      (∑ ω, Real.sqrt (μ.mass ω) ^ 2) = ∑ ω, μ.mass ω := by
        apply Finset.sum_congr rfl
        intro ω _
        exact Real.sq_sqrt (μ.mass_nonneg ω)
      _ = 1 := μ.sum_mass
  have hright : (∑ ω, (Real.sqrt (μ.mass ω) * f ω) ^ 2) =
      μ.expect (fun ω => f ω ^ 2) := by
    rw [expect]
    apply Finset.sum_congr rfl
    intro ω _
    rw [mul_pow, Real.sq_sqrt (μ.mass_nonneg ω)]
  rw [hleft, hmass, hright, one_mul] at hcs
  exact hcs
end FD1D.FiniteLaw
