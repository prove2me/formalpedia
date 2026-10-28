-- Prove2me | solution 1 for AvramDividend.Classical.scale_renewal_laplace_geometric_series
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T21:27:28.015094+00:00
-- url     : https://prove2.me/submissions/2dbb93e3-c627-487f-96e9-9e5deea09d38

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical

/-- Laplace-transform geometric sum for a q-scale renewal series. -/
theorem solution
    (q ψ : ℝ) (hq : 0 ≤ q) (hψ : 0 < ψ) (hqψ : q < ψ) :
    (∑' n : ℕ, q ^ n * (ψ⁻¹) ^ (n + 1)) = (ψ - q)⁻¹ := by
  have hr0 : 0 ≤ q / ψ := div_nonneg hq hψ.le
  have hr1 : q / ψ < 1 :=
    (div_lt_iff₀ hψ).2 (by nlinarith)
  have heq (n : ℕ) :
      ψ⁻¹ * (q / ψ) ^ n = q ^ n * (ψ⁻¹) ^ (n + 1) := by
    simp only [div_eq_mul_inv, mul_pow, pow_succ]
    ring
  have hfuneq :
      (fun n : ℕ => ψ⁻¹ * (q / ψ) ^ n) =
      (fun n : ℕ => q ^ n * (ψ⁻¹) ^ (n + 1)) :=
    funext heq
  have hs : HasSum
      (fun n : ℕ => q ^ n * (ψ⁻¹) ^ (n + 1))
      (ψ⁻¹ * (1 - q / ψ)⁻¹) := by
    have hgeom := (hasSum_geometric_of_lt_one hr0 hr1).mul_left ψ⁻¹
    exact hfuneq ▸ hgeom
  rw [hs.tsum_eq]
  have hψne : ψ ≠ 0 := ne_of_gt hψ
  have hdne : ψ - q ≠ 0 := ne_of_gt (sub_pos.mpr hqψ)
  have hsub : 1 - q / ψ = (ψ - q) / ψ := by
    field_simp
  rw [hsub]
  field_simp [hψne, hdne]
