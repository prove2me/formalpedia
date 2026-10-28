-- Prove2me | solution 1 for AvramDividend.Classical.bv_esscher_root_slack_contraction_parameter
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T09:16:35.371513+00:00
-- url     : https://prove2.me/submissions/3b29e4e6-431e-44cd-bece-e753871cd523

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_bv_esscher_root_subcritical_kernel_mass
import Theorems.Thm_AvramDividend_Classical_bv_esscher_positive_tail_real_total_mass_of_root
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hbv : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
      ((∫ t in Ioi (0 : ℝ),
        ENNReal.toReal (((X.ν.map (fun y : ℝ => Real.toNNReal (-y))).withDensity
          (fun z : ℝ≥0 => ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))))
          {z : ℝ≥0 | t < (z : ℝ)}) ∂volume) / X.drift) < ρ := by
  rw [AvramDividend.Classical.bv_esscher_positive_tail_real_total_mass_of_root X hbv q hq φ hφ
    hroot]
  have hd := (AvramDividend.Classical.bv_standing_drift_pos X hX hbv).1
  have hlt := (AvramDividend.Classical.bv_esscher_root_subcritical_kernel_mass X hbv q hq φ hφ
    hroot).2
  have h0 : 0 ≤ ∫ z : ℝ≥0, (z : ℝ) * Real.exp (-(φ * (z : ℝ)))
      ∂(X.ν.map (fun y : ℝ => Real.toNNReal (-y))) :=
    integral_nonneg fun z => mul_nonneg z.2 (Real.exp_pos _).le
  set I := ∫ z : ℝ≥0, (z : ℝ) * Real.exp (-(φ * (z : ℝ)))
      ∂(X.ν.map (fun y : ℝ => Real.toNNReal (-y)))
  have hr0 : 0 ≤ I / X.drift := div_nonneg h0 hd.le
  have hr1 : I / X.drift < 1 := (div_lt_one hd).mpr hlt
  exact ⟨(I / X.drift + 1) / 2, by linarith, by linarith, by linarith⟩
