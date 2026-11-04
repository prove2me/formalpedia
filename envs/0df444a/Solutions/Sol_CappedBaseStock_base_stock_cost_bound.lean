-- Prove2me | solution 1 for CappedBaseStock.base_stock_cost_bound
-- status  : ACCEPTED   (prove)
-- author  : @StellaXin
-- created : 2026-09-08T02:24:46.770494+00:00
-- url     : https://prove2.me/submissions/4bb71c0a-01e6-4c3b-acc0-49525c6be8d7

import Theorems.Thm_CappedBaseStock_base_stock_average_loss_scan
import Theorems.Thm_CappedBaseStock_scan_excess_certificate_bound
import Theorems.Thm_CappedBaseStock_base_stock_cost_of_loss_bound

/-! Proposition 3 reduces to a scan bound on average lost sales, a certificate
bound on the scan excess, and the inventory-balance conversion to total cost. -/

open MeasureTheory
open scoped ENNReal NNReal
open CappedBaseStock

theorem solution (P : DemandLaw) (c : Parameters) (r z : ℝ)
    (feasible : CertificateFeasible P c r z) :
    baseStockCost P c (Real.toNNReal (((c.L : ℝ) + 1) * r + 2 * z)) ≤
      ENNReal.ofReal (2 * c.h * z +
        ((2 - 1 / ((c.L : ℝ) + 1)) * c.p + c.h * (c.L : ℝ)) * (mean P - r)) := by
  have hL : 0 < (c.L : ℝ) + 1 := by positivity
  have hr : 0 ≤ r := feasible.1
  have hz : 0 ≤ z := feasible.2.2.1
  have hdelta : 0 ≤ mean P - r := sub_nonneg.mpr feasible.2.1
  have hS : 0 ≤ ((c.L : ℝ) + 1) * r + 2 * z := by positivity
  have hcoef : 0 ≤ 2 - 1 / ((c.L : ℝ) + 1) := by
    have hinv : 1 / ((c.L : ℝ) + 1) ≤ 1 := by
      apply (div_le_iff₀ hL).2
      simp only [one_mul]
      linarith [Nat.cast_nonneg (α := ℝ) c.L]
    linarith
  have hell : 0 ≤ (2 - 1 / ((c.L : ℝ) + 1)) * (mean P - r) :=
    mul_nonneg hcoef hdelta
  have hden : ENNReal.ofReal ((c.L : ℝ) + 1) = (c.L : ℝ≥0∞) + 1 := by
    rw [ENNReal.ofReal_add (Nat.cast_nonneg c.L) zero_le_one,
      ENNReal.ofReal_natCast, ENNReal.ofReal_one]
  have hquot :
      (2 * (c.L : ℝ) + 1) * (mean P - r) / ((c.L : ℝ) + 1) =
      (2 - 1 / ((c.L : ℝ) + 1)) * (mean P - r) := by
    field_simp [ne_of_gt hL]
    ring
  have hloss :
      baseStockAverageLoss P c (Real.toNNReal (((c.L : ℝ) + 1) * r + 2 * z)) ≤
        ENNReal.ofReal ((2 - 1 / ((c.L : ℝ) + 1)) * (mean P - r)) := by
    calc
      _ ≤ (∫⁻ d, scanExcess d c.L
          (Real.toNNReal (((c.L : ℝ) + 1) * r + 2 * z) : ℝ) ∂demandPathLaw P) /
          ((c.L : ℝ≥0∞) + 1) := base_stock_average_loss_scan P c _
      _ = (∫⁻ d, scanExcess d c.L
          (((c.L : ℝ) + 1) * r + 2 * z) ∂demandPathLaw P) /
          ((c.L : ℝ≥0∞) + 1) := by rw [Real.coe_toNNReal _ hS]
      _ ≤ ENNReal.ofReal ((2 * (c.L : ℝ) + 1) * (mean P - r)) /
          ((c.L : ℝ≥0∞) + 1) :=
        ENNReal.div_le_div_right (scan_excess_certificate_bound P c r z feasible) _
      _ = ENNReal.ofReal ((2 * (c.L : ℝ) + 1) * (mean P - r) /
          ((c.L : ℝ) + 1)) := by
        rw [← hden, ← ENNReal.ofReal_div_of_pos hL]
      _ = _ := by rw [hquot]
  have hcost := base_stock_cost_of_loss_bound P c
    (Real.toNNReal (((c.L : ℝ) + 1) * r + 2 * z))
    ((2 - 1 / ((c.L : ℝ) + 1)) * (mean P - r)) hell hloss
  rw [Real.coe_toNNReal _ hS] at hcost
  have halgebra :
      c.h * ((((c.L : ℝ) + 1) * r + 2 * z) - ((c.L : ℝ) + 1) * mean P) +
        (c.p + c.h * ((c.L : ℝ) + 1)) *
          ((2 - 1 / ((c.L : ℝ) + 1)) * (mean P - r)) =
      2 * c.h * z +
        ((2 - 1 / ((c.L : ℝ) + 1)) * c.p + c.h * (c.L : ℝ)) * (mean P - r) := by
    field_simp [ne_of_gt hL]
    ring
  rwa [halgebra] at hcost
