-- Prove2me | solution 1 for GaussianPerimeter.tendsto_no_success
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:11:24.927822+00:00
-- url     : https://prove2.me/submissions/7f583f01-f4c2-4cf0-ba9b-db5b1af83363

module
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Topology.Order.LiminfLimsup
public import Definitions.Def_GaussianPerimeter_Basic

set_option autoImplicit true
@[expose] public section
public section
open Filter MeasureTheory
open scoped ENNReal Topology
open GaussianPerimeter
namespace GaussianPerimeter
theorem _root_.solution {q : ℕ → ℝ} {m : ℕ → ℕ} {c : ℝ}
    (hq : Tendsto q atTop (𝓝 0)) (hpos : ∀ᶠ n in atTop, 0 < q n)
    (hmq : Tendsto (fun n => (m n : ℝ) * q n) atTop (𝓝 c)) :
    Tendsto (fun n => (1 - q n) ^ m n) atTop (𝓝 (Real.exp (-c))) := by
  have hq' : Tendsto q atTop (𝓝[Set.Ioi 0] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hq, hpos⟩
  have hInv := tendsto_inv_nhdsGT_zero.comp hq'
  have hLog := (Real.tendsto_mul_log_one_add_div_atTop (-1)).comp hInv
  have h := (Real.continuous_exp.tendsto (c * -1)).comp (hmq.mul hLog)
  rw [mul_neg_one] at h
  apply h.congr'
  filter_upwards [hpos, hq.eventually_lt_const (show (0 : ℝ) < 1 by norm_num)] with n hn hn₁
  change Real.exp ((m n * q n) * ((q n)⁻¹ * Real.log (1 + -1 / (q n)⁻¹))) =
    (1 - q n) ^ m n
  rw [div_inv_eq_mul, neg_one_mul, ← sub_eq_add_neg, ← mul_assoc,
    mul_inv_cancel_right₀ hn.ne', mul_comm, ← Real.rpow_def_of_pos (sub_pos.mpr hn₁),
    Real.rpow_natCast]
end GaussianPerimeter
