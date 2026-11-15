-- Prove2me | solution 2 for AvramDividend.Classical.avram_a71_original_gaussian_physical_negative_jump_independence_20261114
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T23:32:01.375922+00:00
-- url     : https://prove2.me/submissions/eb6a88a9-11a2-447b-9ff1-5614d9e01506
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a95_original_intrinsic_gaussian_vs_physical_full_negative_jump_independent_20261114
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hPositive : 0 < X.σ) (hNu : X.ν ≠ 0)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω)))
    (t : ℝ≥0) (ht : 0 < t) (θ : ℝ) (hθ : 0 < θ)
    (H J : Ω → ℝ)
    (hHMeas : Measurable H) (hJMeas : Measurable J)
    (hHEq : H =ᵐ[P] R t)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0,
        if 0 < u ∧ u ≤ t then
          X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
        else 0)
    (hDecomp : ∀ ω, H ω + J ω =
      X.X t ω -
        (t : ℝ) * (X.c - ∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν)) :
    IndepFun (fun ω => Real.exp (θ * H ω))
      (fun ω => Real.exp (θ * J ω)) P := by
  have hIndep : IndepFun H J P :=
    avram_a95_original_intrinsic_gaussian_vs_physical_full_negative_jump_independent_20261114
      X hX hFinite hPositive hNu R hR t ht H J hHMeas hJMeas hHEq hJEq
  have hExp : Measurable (fun x : ℝ => Real.exp (θ * x)) := by fun_prop
  simpa only [Function.comp_def] using hIndep.comp hExp hExp
