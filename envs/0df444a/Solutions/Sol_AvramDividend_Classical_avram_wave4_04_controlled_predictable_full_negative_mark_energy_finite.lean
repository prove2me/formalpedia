-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04_controlled_predictable_full_negative_mark_energy_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T19:27:36.508989+00:00
-- url     : https://prove2.me/submissions/b11467ca-b717-4f43-8d86-fcfcbcfe66c5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_source_full_negative_mark_uniform_quadratic_envelope
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v δ : ℝ)
    (hw : ContDiffOn ℝ 1 w (Ioo a b))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (hu0 : 0 ≤ u)
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hband : u + δ ≤ v)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ :=
      fun p => if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0
    Measurable[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)] H ∧
    (∫⁻ p : ℝ≥0 × Ω,
      ∫⁻ z in Iio (0 : ℝ),
        ENNReal.ofReal ((H (p, z)) ^ 2) ∂X.ν ∂μ) < ⊤ := by
  dsimp only
  have hw_meas : Measurable w := by
    have hmax : Continuous (fun y : ℝ => max y 0) := continuous_id.max continuous_const
    have hcomp : Continuous (fun y : ℝ => w (max y 0)) :=
      hw_cont.comp_continuous hmax (by intro y; exact le_max_right y 0)
    have heq : w = (fun y : ℝ => if y < 0 then 0 else w (max y 0)) := by
      funext y
      by_cases hy : y < 0
      · simp [hy, hw_neg y hy]
      · simp [hy, max_eq_left (le_of_not_gt hy)]
    rw [heq]
    exact measurable_const.ite measurableSet_Iio hcomp.measurable
  obtain ⟨K, hK, hpoint, _⟩ :=
    avram_wave4_04_source_full_negative_mark_uniform_quadratic_envelope
      X w a b u v δ hw hw_cont hw_neg hau huv hvb hu0 hδ hδone hband
  have hPre : IsStronglyPredictable 𝓕.rightCont
      (fun t ω => Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s ω - rightLimit D s ω) t) :=
    avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable X x D hD
  change StronglyMeasurable[𝓕.rightCont.predictable] (fun p : ℝ≥0 × Ω =>
    Function.leftLim (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) at hPre
  have hY : Measurable[𝓕.rightCont.predictable] (fun p : ℝ≥0 × Ω =>
      Function.leftLim (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) :=
    hPre.measurable
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  letI : MeasurableSpace ((ℝ≥0 × Ω) × ℝ) := (𝓕.rightCont.predictable).prod (inferInstance : MeasurableSpace ℝ)
  have hYmark : Measurable (fun p : ((ℝ≥0 × Ω) × ℝ) =>
      Function.leftLim (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1) :=
    hY.comp measurable_fst
  have hbandm : MeasurableSet {p : ((ℝ≥0 × Ω) × ℝ) |
      Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1 ∈ Icc (u + δ) v} :=
    measurableSet_Icc.preimage hYmark
  have hkernel : Measurable (fun p : ((ℝ≥0 × Ω) × ℝ) =>
      w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1
        + p.2) -
      w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1)) :=
    (hw_meas.comp (hYmark.add measurable_snd)).sub (hw_meas.comp hYmark)
  have hHmeas : Measurable (fun p : ((ℝ≥0 × Ω) × ℝ) =>
      if Function.leftLim
          (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1
          ∈ Icc (u + δ) v then
        w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1
          + p.2) -
        w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1)
      else 0) :=
    hkernel.ite hbandm measurable_const
  refine ⟨hHmeas, ?_⟩
  have hνmeas : Measurable (fun z : ℝ => ENNReal.ofReal (min 1 (z ^ 2))) := by fun_prop
  have hM : ENNReal.ofReal K * (∫⁻ z : ℝ, ENNReal.ofReal (min 1 (z ^ 2)) ∂X.ν) < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top X.ν_integrable
  have hinner (p : ℝ≥0 × Ω) :
      (∫⁻ z in Iio (0 : ℝ),
        ENNReal.ofReal
          ((if Function.leftLim
              (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
              ∈ Icc (u + δ) v then
              w (Function.leftLim
                (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
                + z) -
              w (Function.leftLim
                (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1)
            else 0) ^ 2) ∂X.ν) ≤
      ENNReal.ofReal K *
        (∫⁻ z : ℝ, ENNReal.ofReal (min 1 (z ^ 2)) ∂X.ν) := by
    have hpoint' (z : ℝ) (hz : z ∈ Iio (0 : ℝ)) :
        ENNReal.ofReal
          ((if Function.leftLim
              (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
              ∈ Icc (u + δ) v then
              w (Function.leftLim
                (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 + z) -
              w (Function.leftLim
                (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1)
            else 0) ^ 2) ≤
          ENNReal.ofReal K *
            ENNReal.ofReal (min 1 (z ^ 2)) := by
      by_cases hb :
          Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
            ∈ Icc (u + δ) v
      · simp only [if_pos hb]
        rw [← ENNReal.ofReal_mul hK]
        exact ENNReal.ofReal_le_ofReal
          (hpoint _ hb z hz)
      · simp only [if_neg hb, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
          ENNReal.ofReal_zero]
        exact bot_le
    calc
      (∫⁻ z in Iio (0 : ℝ), _ ∂X.ν) ≤
          ∫⁻ z in Iio (0 : ℝ),
            ENNReal.ofReal K * ENNReal.ofReal (min 1 (z ^ 2)) ∂X.ν := by
              apply setLIntegral_mono (by fun_prop)
              intro z hz
              exact hpoint' z hz
      _ ≤ ∫⁻ z : ℝ,
            ENNReal.ofReal K * ENNReal.ofReal (min 1 (z ^ 2)) ∂X.ν :=
        setLIntegral_le_lintegral _ _
      _ = _ := lintegral_const_mul _ hνmeas
  calc
    (∫⁻ p : ℝ≥0 × Ω, ∫⁻ z in Iio (0 : ℝ), _ ∂X.ν ∂μ)
        ≤ ∫⁻ p : ℝ≥0 × Ω,
          ENNReal.ofReal K *
            (∫⁻ z : ℝ, ENNReal.ofReal (min 1 (z ^ 2)) ∂X.ν) ∂μ :=
        lintegral_mono hinner
    _ = μ Set.univ *
          (ENNReal.ofReal K *
            (∫⁻ z : ℝ, ENNReal.ofReal (min 1 (z ^ 2)) ∂X.ν)) := by simp [mul_comm]
    _ < ⊤ := ENNReal.mul_lt_top hμ hM