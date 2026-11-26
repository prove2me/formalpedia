-- Prove2me | solution 1 for FD1D.transport_cost_equation_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:03:22.424459+00:00
-- url     : https://prove2.me/submissions/cd494e25-ea3c-445c-9bd5-e8d0cbaf6613

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
import Theorems.Thm_FD1D_expected_haarL2
import Theorems.Thm_FD1D_expected_area_le_sqrt_l2
import Theorems.Thm_FD1D_FiniteLaw_expect_mono


set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]
namespace FD1D
theorem _root_.solution
    (μ : FiniteLaw Ω) (l p : ι → ℝ) (b : Ω → ι → ℝ)
    (cost : Ω → ℝ) (n a gap : ℝ)
    (_hn : 0 < n) (ha : 0 ≤ a) (hgap : 0 ≤ gap)
    (hp : ∀ i, 0 < p i)
    (hcost : ∀ ω, cost ω ≤ 1 / n +
      cdfTransportArea (haarCombination l p (b ω)))
    (hsym : ∀ i j, i ≠ j → IntervalsSeparated l p i j ∨
      μ.OddSymmetry (fun ω => b ω i * b ω j))
    (htelescope : ∑ i, p i * μ.expect (fun ω => (b ω i) ^ 2) ≤
      2 * a ^ 2 * gap) :
    μ.expect cost ≤ 1 / n + a / Real.sqrt 6 * Real.sqrt gap := by
  have hcostExpect : μ.expect cost ≤ 1 / n +
      μ.expect (fun ω => cdfTransportArea (haarCombination l p (b ω))) := by
    calc
      μ.expect cost ≤ μ.expect (fun ω => 1 / n +
          cdfTransportArea (haarCombination l p (b ω))) :=
        μ.expect_mono hcost
      _ = 1 / n + μ.expect (fun ω =>
          cdfTransportArea (haarCombination l p (b ω))) := by
        rw [FiniteLaw.expect, FiniteLaw.expect]
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib, ← Finset.sum_mul]
        rw [μ.sum_mass, one_mul]
  have harea := expected_area_le_sqrt_l2 μ l p b hp
  have hhaar := expected_haarL2 μ l p b hp hsym
  have hl2 : μ.expect (fun ω => haarL2 l p (b ω)) ≤ a ^ 2 * gap / 6 := by
    rw [hhaar]
    nlinarith
  have hsqrt6 : 0 < Real.sqrt 6 := Real.sqrt_pos.2 (by norm_num)
  have hcoef_nonneg : 0 ≤ a / Real.sqrt 6 * Real.sqrt gap := by positivity
  have hcoef_sq :
      (a / Real.sqrt 6 * Real.sqrt gap) ^ 2 = a ^ 2 * gap / 6 := by
    rw [mul_pow, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6),
      Real.sq_sqrt hgap]
    ring
  have hsqrtBound : Real.sqrt (μ.expect (fun ω => haarL2 l p (b ω))) ≤
      a / Real.sqrt 6 * Real.sqrt gap := by
    rw [Real.sqrt_le_iff]
    exact ⟨hcoef_nonneg, hcoef_sq ▸ hl2⟩
  linarith
end FD1D
