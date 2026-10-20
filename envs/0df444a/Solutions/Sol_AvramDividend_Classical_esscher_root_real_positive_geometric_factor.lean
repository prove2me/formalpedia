-- Prove2me | solution 1 for AvramDividend.Classical.esscher_root_real_positive_geometric_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T17:38:52.718809+00:00
-- url     : https://prove2.me/submissions/13b4d37e-f18a-4497-8454-04b8aa6f5e32

import Theorems.Thm_AvramDividend_Classical_positive_geometric_transform_real_reciprocal
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-!
The real/ENNReal scalar bridge for the positive Esscher root.
All analytic assumptions are explicit; the parent will prove them.
-/
theorem solution
    (μ : Measure ℝ≥0) (φ δ s q ψval : ℝ)
    (hδ : 0 < δ) (hs : 0 < s)
    (hint : Integrable
      (fun z : ℝ≥0 => Real.exp (-(φ * (z : ℝ))) *
        (1 - Real.exp (-(s * (z : ℝ))))) μ)
    (hψ : ψval - q = δ * s -
       (∫ z : ℝ≥0, Real.exp (-(φ * (z : ℝ))) *
          (1 - Real.exp (-(s * (z : ℝ)))) ∂μ))
    (r : ℝ≥0∞)
    (hr : r = ∫⁻ z : ℝ≥0,
        ENNReal.ofReal (Real.exp (-(φ * (z : ℝ)))) *
          ENNReal.ofReal ((1 - Real.exp (-(s * (z : ℝ)))) / s) ∂μ)
    (hgap : r < ENNReal.ofReal δ) :
    q < ψval ∧
      ENNReal.ofReal (1 / s) *
        ((ENNReal.ofReal δ)⁻¹ *
          (1 - (ENNReal.ofReal δ)⁻¹ * r)⁻¹) =
        ENNReal.ofReal ((ψval - q)⁻¹) := by
  let f : ℝ≥0 → ℝ := fun z =>
    Real.exp (-(φ * (z : ℝ))) * (1 - Real.exp (-(s * (z : ℝ))))
  have hfnonneg : 0 ≤ᵐ[μ] f := by
    filter_upwards with z
    dsimp [f]
    have hz : 0 ≤ (z : ℝ) := z.property
    have hexp : Real.exp (-(s * (z : ℝ))) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith)
    exact mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr hexp)
  let J : ℝ := ∫ z : ℝ≥0, f z ∂μ
  have hJ0 : 0 ≤ J := integral_nonneg_of_ae hfnonneg
  have hdivint : Integrable (fun z : ℝ≥0 => f z / s) μ :=
    hint.div_const s
  have hdivpos : 0 ≤ᵐ[μ] fun z : ℝ≥0 => f z / s := by
    filter_upwards [hfnonneg] with z hz
    exact div_nonneg hz hs.le
  have hdiv : (∫⁻ z : ℝ≥0, ENNReal.ofReal (f z / s) ∂μ) =
      ENNReal.ofReal (J / s) := by
    have h := ofReal_integral_eq_lintegral_ofReal hdivint hdivpos
    rw [integral_div] at h
    exact h.symm
  have hK : r = ENNReal.ofReal (J / s) := by
    rw [hr]
    calc
      _ = ∫⁻ z : ℝ≥0, ENNReal.ofReal (f z / s) ∂μ := by
        apply lintegral_congr
        intro z
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
        congr 1
        dsimp [f]
        ring
      _ = ENNReal.ofReal (J / s) := hdiv
  have hJlt : J < δ * s := by
    have hreal : J / s < δ := by
      apply (ENNReal.ofReal_lt_ofReal_iff hδ).mp
      rw [← hK]
      exact hgap
    exact (div_lt_iff₀ hs).mp hreal
  have hψpos : q < ψval := by
    apply sub_pos.mp
    rw [hψ]
    exact sub_pos.mpr hJlt
  have hsc := positive_geometric_transform_real_reciprocal
    δ s J hδ hs hJ0 hJlt
  refine ⟨hψpos, ?_⟩
  rw [hK, hψ]
  exact hsc
