-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03b_actual_ruin_stopped_C2_signed_intrinsic_separated_band_eq_finite_source_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T15:25:24.531528+00:00
-- url     : https://prove2.me/submissions/4f3fdb64-4cae-4074-be59-94948e696cdf

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_separated_band_absolute_taylor_intrinsic_eq_finite_source_sum
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_intrinsic_signed_finite_band_integral_eq_actual_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_full_negative_C2_taylor_predictable_L1_L2

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- Each original stopped C² source band has automatically integrable signed
Taylor correction; its intrinsic signed integral is its true finite jump sum. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
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
    (s t : ℝ≥0) (ω : Ω)
    (B : Set ℝ) (hBm : MeasurableSet B)
    (hBneg : B ⊆ Iio (0 : ℝ))
    (ε : ℝ) (hε : 0 < ε)
    (hBsep : ∀ z ∈ B, ε ≤ dist z 0) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun r : ℝ≥0 => x + X.X r p.2 - rightLimit D r p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0) -
      (if -1 < p.2 then
        p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
        else 0)
    let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
    let J : ℝ≥0 → Ω → ℝ := fun r η =>
      X.X r η - Function.leftLim (fun z : ℝ≥0 => X.X z η) r
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun η =>
      ((Measure.count.restrict {r : ℝ≥0 | 0 < r ∧ J r η ≠ 0}).map
        (fun r : ℝ≥0 => (r, J r η)))
    let G : ℝ≥0 × ℝ → ℝ := fun p =>
      if s < p.1 ∧ p.1 ≤ t ∧ p.2 ∈ B then HS ((p.1,ω),p.2) else 0
    ∃ T : Finset ℝ≥0,
      (∀ r : ℝ≥0, r ∈ T ↔ s < r ∧ r ≤ t ∧ J r ω ∈ B) ∧
      Integrable G (NX ω) ∧
      (∫ p : ℝ≥0 × ℝ, G p ∂NX ω) =
        ∑ r ∈ T, HS ((r,ω),J r ω) := by
  let Y : ℝ≥0 × Ω → ℝ := fun p =>
    Function.leftLim (fun r : ℝ≥0 => x + X.X r p.2 - rightLimit D r p.2) p.1
  let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    (if Y p.1 ∈ Icc (u + δ) v then w (Y p.1 + p.2) - w (Y p.1) else 0) -
    (if -1 < p.2 then p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0) else 0)
  let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
  let J : ℝ≥0 → Ω → ℝ := fun r η =>
    X.X r η - Function.leftLim (fun z : ℝ≥0 => X.X z η) r
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun η =>
    ((Measure.count.restrict {r : ℝ≥0 | 0 < r ∧ J r η ≠ 0}).map
      (fun r : ℝ≥0 => (r, J r η)))
  let f : (ℝ≥0 × ℝ) → ℝ := fun p => HS ((p.1,ω),p.2)
  let G : ℝ≥0 × ℝ → ℝ := fun p =>
    if s < p.1 ∧ p.1 ≤ t ∧ p.2 ∈ B then f p else 0
  change ∃ T : Finset ℝ≥0,
      (∀ r : ℝ≥0, r ∈ T ↔ s < r ∧ r ≤ t ∧ J r ω ∈ B) ∧
      Integrable G (NX ω) ∧
      (∫ p : ℝ≥0 × ℝ, G p ∂NX ω) =
        ∑ r ∈ T, HS ((r,ω),J r ω)
  obtain ⟨T, hT, hAbs⟩ :=
    avram_wave5_03b_actual_separated_band_absolute_taylor_intrinsic_eq_finite_source_sum
      X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv
      s t ω B hBm hBneg ε hε hBsep
  have hμ : (0 : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable)) Set.univ < ⊤ := by simp
  have hHS : Measurable[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)] HS := by
    simpa [HS, H, Y] using
      (avram_wave5_03b_actual_ruin_stopped_full_negative_C2_taylor_predictable_L1_L2
        X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv
        (0 : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable)) hμ).1
  have hPredLeProd :
      (𝓕.rightCont.predictable) ≤ (inferInstance : MeasurableSpace (ℝ≥0 × Ω)) :=
    measurableSpace_le_predictable_of_measurableSet
      (fun A hA => (measurableSet_singleton (⊥ : ℝ≥0)).prod ((𝓕.rightCont.le ⊥) A hA))
      (fun i A hA => measurableSet_Ioi.prod ((𝓕.rightCont.le i) A hA))
  have hHSStd : Measurable HS := by
    letI : MeasurableSpace ((ℝ≥0 × Ω) × ℝ) :=
      (𝓕.rightCont.predictable).prod (inferInstance : MeasurableSpace ℝ)
    exact hHS.mono
      (sup_le_sup (MeasurableSpace.comap_mono hPredLeProd) le_rfl) le_rfl
  have hf : Measurable f :=
    hHSStd.comp ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)
  have hcond : MeasurableSet {p : ℝ≥0 × ℝ |
      s < p.1 ∧ p.1 ≤ t ∧ p.2 ∈ B} := by
    have hfst : Measurable (fun p : ℝ≥0 × ℝ => p.1) := measurable_fst
    have hsnd : Measurable (fun p : ℝ≥0 × ℝ => p.2) := measurable_snd
    exact (measurableSet_Ioi.preimage hfst).inter
      ((measurableSet_Iic.preimage hfst).inter (hBm.preimage hsnd))
  have hG : Measurable G := by
    simpa [G] using Measurable.ite hcond hf measurable_const
  have hAbsG : (∫⁻ p : ℝ≥0 × ℝ, ENNReal.ofReal (|G p|) ∂NX ω) =
      ∑ r ∈ T, ENNReal.ofReal (|HS ((r,ω),J r ω)|) := by
    calc
      _ = ∫⁻ p : ℝ≥0 × ℝ,
        (if s < p.1 ∧ p.1 ≤ t ∧ p.2 ∈ B then
          ENNReal.ofReal (|HS ((p.1,ω),p.2)|) else 0) ∂NX ω := by
          apply lintegral_congr
          intro p
          by_cases hp : s < p.1 ∧ p.1 ≤ t ∧ p.2 ∈ B
          · simp [G, f, hp]
          · simp [G, hp]
      _ = _ := hAbs
  have hFiniteSum :
      (∑ r ∈ T, ENNReal.ofReal (|HS ((r,ω),J r ω)|)) < ⊤ := by
    apply (ENNReal.sum_lt_top).2
    intro r hr
    simp
  have hFiniteIntegral :
      (∫⁻ p : ℝ≥0 × ℝ, ENNReal.ofReal (|G p|) ∂NX ω) < ⊤ :=
    lt_of_eq_of_lt hAbsG hFiniteSum
  have hHasFinite : HasFiniteIntegral G (NX ω) := by
    unfold HasFiniteIntegral
    simpa only [Real.enorm_eq_ofReal_abs] using hFiniteIntegral
  have hIntegrable : Integrable G (NX ω) :=
    ⟨hG.aestronglyMeasurable, hHasFinite⟩
  refine ⟨T, hT, hIntegrable, ?_⟩
  simpa only [G, f, J, NX] using
    (avram_wave5_03_original_intrinsic_signed_finite_band_integral_eq_actual_jump_sum
      X ω s t B hBm hBneg T hT f hf hIntegrable)
