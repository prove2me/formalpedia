-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_02_actual_discounted_stopped_Taylor_source_cutoff_L1_error_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T06:35:51.814965+00:00
-- url     : https://prove2.me/submissions/53ca1309-846a-43bd-9772-08ec75133cbf

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_discounted_stopped_Taylor_source_cutoff_Lp2_error_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤) :
    let a : (ℝ≥0 × Ω) → ℝ := fun p =>
      if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) else 0
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0) -
      (if -1 < p.2 then
        p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
        else 0)
    let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
    let GW : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p => a p.1 * HS p
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      let hML : MemLp GW (2 : ℝ≥0∞) (μ.prod (X.ν.restrict (Iio (0 : ℝ)))) :=
        avram_wave6_02_actual_discounted_ruin_stopped_Taylor_rightcont_product_MemLp
          X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv q hq T μ hμ;
      ∀ (A : Set (((ℝ≥0 × Ω) × ℝ))) (hA : MeasurableSet A)
        (I : Lp ℝ (2 : ℝ≥0∞) (μ.prod (X.ν.restrict (Iio (0 : ℝ)))) →ₗ[ℝ]
          Lp ℝ (2 : ℝ≥0∞) P)
        (hIso : ∀ v, ‖I v‖ = ‖v‖),
      (∫ ω, |((I ((hML.indicator hA).toLp (A.indicator GW)) -
          I (hML.toLp GW)) ω : ℝ)| ∂P) ≤
          (eLpNorm (Aᶜ.indicator GW) (2 : ℝ≥0∞)
            (μ.prod (X.ν.restrict (Iio (0 : ℝ))))).toReal)  := by
  classical
  intro a Y H HS GW
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  intro hML A hA I hIso
  let F : Lp ℝ (2 : ℝ≥0∞) P :=
    I ((hML.indicator hA).toLp (A.indicator GW)) - I (hML.toLp GW)
  have hFm : AEStronglyMeasurable (fun ω => (F ω : ℝ)) P :=
    (Lp.memLp F).1
  have hCompare :
      eLpNorm (fun ω => (F ω : ℝ)) (1 : ℝ≥0∞) P ≤
      eLpNorm (fun ω => (F ω : ℝ)) (2 : ℝ≥0∞) P :=
    eLpNorm_le_eLpNorm_of_exponent_le
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hFm
  have hFin :
      eLpNorm (fun ω => (F ω : ℝ)) (2 : ℝ≥0∞) P ≠ ⊤ :=
    ne_top_of_lt (Lp.eLpNorm_lt_top F)
  have hL1 : (∫ ω, |(F ω : ℝ)| ∂P) ≤ ‖F‖ := by
    calc
      (∫ ω, |(F ω : ℝ)| ∂P) =
          (eLpNorm (fun ω => (F ω : ℝ)) (1 : ℝ≥0∞) P).toReal := by
        simpa only [Real.norm_eq_abs, eLpNorm_one_eq_lintegral_enorm] using
          (integral_norm_eq_lintegral_enorm hFm)
      _ ≤ (eLpNorm (fun ω => (F ω : ℝ)) (2 : ℝ≥0∞) P).toReal :=
        ENNReal.toReal_mono hFin hCompare
      _ = ‖F‖ := (Lp.norm_def F).symm
  have hCut : ‖F‖ ≤
      (eLpNorm (Aᶜ.indicator GW) (2 : ℝ≥0∞)
        (μ.prod (X.ν.restrict (Iio (0 : ℝ))))).toReal := by
    exact avram_wave6_02_actual_discounted_stopped_Taylor_source_cutoff_Lp2_error_bound
      X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv q hq T μ hμ
      A hA I hIso
  exact le_trans hL1 hCut
