-- Prove2me | solution 1 for ClassicalComplexWPT.eval_weightedCoefficientSeries_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:09:49.698738+00:00
-- url     : https://prove2.me/submissions/b092d3e4-1b83-4d8c-a2c5-deefa8a6102d

import Definitions.Def_ClassicalComplexWPT_WeightedCoefficientMap
import Definitions.Def_ClassicalComplexWPT_L1PowerSeries
import Definitions.Def_ClassicalComplexWPT_WeightedEvaluation
import Theorems.Thm_ClassicalComplexWPT_evalL1PowerSeries_eq_tsum
import Theorems.Thm_ClassicalComplexWPT_lastAxis_apply
import Theorems.Thm_ClassicalComplexWPT_lastSlice_zero
import Theorems.Thm_ClassicalComplexWPT_monomial_zero
import Theorems.Thm_ClassicalComplexWPT_weightedCoefficientSeries_sum_apply_lastTaylorCoefficient
import Theorems.Thm_ClassicalComplexWPT_weightedLastCoeffs_apply
attribute [local simp] ClassicalComplexWPT.lastAxis_apply
attribute [local simp] ClassicalComplexWPT.lastSlice_zero
attribute [local simp] ClassicalComplexWPT.monomial_zero
attribute [local simp] ClassicalComplexWPT.weightedLastCoeffs_apply



set_option autoImplicit true
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr0 : 0 < r) (hrp : (r : ℝ≥0∞) < p.radius)
    (z : Base n) (w : ℂ)
    (hzq : z ∈ Metric.eball (0 : Base n) (weightedCoefficientSeries p r).radius)
    (hzw : (‖(z, (0 : ℂ))‖₊ + ‖((0 : Base n), w)‖₊ : ℝ≥0∞) < p.radius)
    (hw : ‖w‖ < r) :
    evalL1PowerSeries ((weightedCoefficientSeries p r).sum z) ((r : ℂ)⁻¹ * w) =
      p.sum (z, w) := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  have hscaled : ‖(r : ℂ)⁻¹ * w‖ < 1 := by
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg r.coe_nonneg]
    exact (inv_mul_lt_one₀ (by exact_mod_cast hr0)).2 (by exact_mod_cast hw)
  rw [evalL1PowerSeries_eq_tsum _ hscaled]
  have hzp : (z, (0 : ℂ)) ∈ Metric.eball (0 : Ambient n) p.radius := by
    rw [mem_eball_zero_iff]
    exact (show (‖(z, (0 : ℂ))‖₊ : ℝ≥0∞) ≤
        ‖(z, (0 : ℂ))‖₊ + ‖((0 : Base n), w)‖₊ by
      exact le_add_right le_rfl).trans_lt hzw
  calc
    (∑' k : ℕ, (weightedCoefficientSeries p r).sum z k * ((r : ℂ)⁻¹ * w) ^ k) =
        ∑' k : ℕ, p.changeOrigin (z, 0) k (fun _ ↦ lastDirection n) * w ^ k := by
      apply tsum_congr
      intro k
      rw [weightedCoefficientSeries_sum_apply_lastTaylorCoefficient p r z k hrp hzq hzp]
      simp only [lastTaylorCoefficient]
      let c : ℂ := p.changeOrigin (z, 0) k (fun _ ↦ lastDirection n)
      change ((r : ℂ) ^ k * c) * ((r : ℂ)⁻¹ * w) ^ k = c * w ^ k
      rw [mul_pow]
      calc
        ((r : ℂ) ^ k * c) * ((r : ℂ)⁻¹ ^ k * w ^ k) =
            (((r : ℂ) ^ k * (r : ℂ)⁻¹ ^ k) * c) * w ^ k := by ring
        _ = c * w ^ k := by rw [← mul_pow]; simp [hrC]
    _ = (p.changeOrigin (z, 0)).sum (0, w) := by
      unfold FormalMultilinearSeries.sum
      apply tsum_congr
      intro k
      rw [show ((0 : Base n), w) = w • lastDirection n by
        ext <;> simp [lastDirection]]
      rw [(p.changeOrigin (z, 0) k).map_smul_univ]
      simp [Finset.prod_const, smul_eq_mul, mul_comm]
    _ = p.sum (z, w) := by
      rw [p.changeOrigin_eval hzw]
      congr 1
      ext <;> simp
end ClassicalComplexWPT
