-- Prove2me | solution 1 for AvramDividend.Classical.avram_a34_original_gaussian_intrinsic_zero_time_charfun_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:07:21.513109+00:00
-- url     : https://prove2.me/submissions/2484eb9d-3fc7-4cd4-957e-2a21e1ed528d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a24_original_gaussian_adapted_zero_origin_20261113
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω)))
    (G : ℝ≥0 → Ω → ℝ)
    (hEq : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, G t ω = R t ω) :
    ∀ u : ℝ,
      charFun (P.map (G 0)) u =
        charFun (gaussianReal 0 0) u := by
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨H, _, hHzero, hHEq⟩ :=
    avram_a24_original_gaussian_adapted_zero_origin_20261113 X R hR
  have hGzero : (G 0) =ᵐ[P] (fun _ : Ω => (0 : ℝ)) := by
    filter_upwards [hHEq, hEq] with ω hHω hGω
    rw [hGω 0, ← hHω 0, hHzero]
  have hMap : P.map (G 0) = gaussianReal 0 0 := by
    calc
      P.map (G 0) = P.map (fun _ : Ω => (0 : ℝ)) :=
        Measure.map_congr hGzero
      _ = Measure.dirac 0 := by simp
      _ = gaussianReal 0 0 := (gaussianReal_zero_var 0).symm
  intro u
  rw [hMap]
