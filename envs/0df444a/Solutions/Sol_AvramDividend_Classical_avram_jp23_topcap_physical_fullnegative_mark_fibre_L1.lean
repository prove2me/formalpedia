-- Prove2me | solution 1 for AvramDividend.Classical.avram_jp23_topcap_physical_fullnegative_mark_fibre_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T23:29:40.773351+00:00
-- url     : https://prove2.me/submissions/3379e180-9eee-4744-a8f7-2f02049b5ed4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jp23_topcap_fullnegative_H_absolute_source_envelope
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hTop : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (q : ℝ) (σ : Ω → ℝ≥0)
    (hFiniteActivity : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    let Y : ℝ≥0 × Ω → ℝ := fun p =>
      Function.leftLim
        (fun r : ℝ≥0 => x + X.X r p.2 - rightLimit D r p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if 0 < p.1.1 ∧ p.1.1 ≤ σ p.1.2 ∧
          (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 ∧
          0 ≤ Y p.1 ∧ ENNReal.ofReal (Y p.1) ≤ C ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (Y p.1 + p.2) - w (Y p.1))
      else 0
    ∀ (t : ℝ≥0) (ω : Ω),
      (∫⁻ z : ℝ, ENNReal.ofReal (‖H ((t, ω), z)‖)
        ∂(X.ν.restrict (Iio (0 : ℝ)))) ≤
          ENNReal.ofReal (Real.exp (-(q * (t : ℝ))) * w (Y (t, ω))) *
            X.ν (Iio (0 : ℝ)) ∧
      (∫⁻ z : ℝ, ENNReal.ofReal (‖H ((t, ω), z)‖)
        ∂(X.ν.restrict (Iio (0 : ℝ)))) < ⊤ := by
  classical
  intro Y H t ω
  have hBound :
      (∫⁻ z : ℝ, ENNReal.ofReal (‖H ((t, ω), z)‖)
        ∂(X.ν.restrict (Iio (0 : ℝ)))) ≤
        ENNReal.ofReal (Real.exp (-(q * (t : ℝ))) * w (Y (t, ω))) *
          X.ν (Iio (0 : ℝ)) := by
    calc
      (∫⁻ z : ℝ, ENNReal.ofReal (‖H ((t, ω), z)‖)
          ∂(X.ν.restrict (Iio (0 : ℝ)))) ≤
          (∫⁻ _z : ℝ,
            ENNReal.ofReal (Real.exp (-(q * (t : ℝ))) * w (Y (t, ω)))
              ∂(X.ν.restrict (Iio (0 : ℝ)))) := by
        apply lintegral_mono
        intro z
        exact ENNReal.ofReal_le_ofReal
          (avram_jp23_topcap_fullnegative_H_absolute_source_envelope
            X x D w C hTop hw0 hw_cont hw_neg hw_grad q σ
            ((t, ω), z))
      _ = _ := by simp [lintegral_const]
  have hFinite :
      ENNReal.ofReal (Real.exp (-(q * (t : ℝ))) * w (Y (t, ω))) *
          X.ν (Iio (0 : ℝ)) < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (lt_top_iff_ne_top.mpr hFiniteActivity)
  exact ⟨hBound, lt_of_le_of_lt hBound hFinite⟩
