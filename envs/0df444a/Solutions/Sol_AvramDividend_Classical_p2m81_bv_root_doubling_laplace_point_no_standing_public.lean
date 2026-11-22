-- Prove2me | solution 1 for AvramDividend.Classical.p2m81_bv_root_doubling_laplace_point_no_standing_public
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T04:12:14.465828+00:00
-- url     : https://prove2.me/submissions/81d4f413-2fa0-4d1c-8fdb-d96ae2b295e4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_laplace_exponent_convexOn_nonnegative
open MeasureTheory Filter Set Topology
open AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    q < X.ψ (2 * φ) := by
  have hconv := levy_laplace_exponent_convexOn_nonnegative X
  have h2mem : (2 * φ) ∈ Ici (0 : ℝ) := mem_Ici.mpr (by positivity)
  have h0mem : (0 : ℝ) ∈ Ici (0 : ℝ) := mem_Ici.mpr le_rfl
  have hψ0 : X.ψ 0 = 0 := by
    simp only [SpectrallyNegativeLevy.ψ, laplaceExponent]
    simp
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hsum : (1 / 2 : ℝ) + 1 / 2 = 1 := by norm_num
  have hj := hconv.2 h0mem h2mem hhalf hhalf hsum
  simp only [smul_eq_mul] at hj
  have harg : (1 / 2 : ℝ) * 0 + (1 / 2) * (2 * φ) = φ := by ring
  rw [harg, hψ0] at hj
  simp only [mul_zero, zero_add] at hj
  nlinarith [hj, hroot, hq]
