-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03b_actual_separated_band_absolute_taylor_intrinsic_eq_finite_source_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T15:01:46.507213+00:00
-- url     : https://prove2.me/submissions/f45bc3c8-463b-465e-8e95-1fe9ee299f9b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_separated_source_band_stopped_ito_balance
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_lintegral_eq_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_full_negative_C2_taylor_predictable_L1_L2

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- The original stopped controlled nonlinear Taylor jump integral on a
separated source band is a finite sum over its true Lévy jump times. -/
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
    ∃ T : Finset ℝ≥0,
      (∀ r : ℝ≥0, r ∈ T ↔ s < r ∧ r ≤ t ∧ J r ω ∈ B) ∧
      (∫⁻ p : ℝ≥0 × ℝ,
        (if s < p.1 ∧ p.1 ≤ t ∧ p.2 ∈ B then
          ENNReal.ofReal (|HS ((p.1,ω),p.2)|) else 0) ∂NX ω) =
      ∑ r ∈ T, ENNReal.ofReal (|HS ((r,ω),J r ω)|) := by
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
  change ∃ T : Finset ℝ≥0,
      (∀ r : ℝ≥0, r ∈ T ↔ s < r ∧ r ≤ t ∧ J r ω ∈ B) ∧
      (∫⁻ p : ℝ≥0 × ℝ,
        (if s < p.1 ∧ p.1 ≤ t ∧ p.2 ∈ B then
          ENNReal.ofReal (|HS ((p.1,ω),p.2)|) else 0) ∂NX ω) =
      ∑ r ∈ T, ENNReal.ofReal (|HS ((r,ω),J r ω)|)
  obtain ⟨T, hT, _⟩ :=
    avram_wave5_03b_actual_separated_source_band_stopped_ito_balance
      X x D hD w u v δ s t ω B hBneg ε hε hBsep
  refine ⟨T, hT, ?_⟩
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
  have hAbsStd : Measurable (fun p : ((ℝ≥0 × Ω) × ℝ) =>
      ENNReal.ofReal (|HS p|)) := by
    letI : MeasurableSpace ((ℝ≥0 × Ω) × ℝ) :=
      (𝓕.rightCont.predictable).prod (inferInstance : MeasurableSpace ℝ)
    have hAbs : Measurable (fun p : ((ℝ≥0 × Ω) × ℝ) =>
        ENNReal.ofReal (|HS p|)) := ENNReal.measurable_ofReal.comp hHS.abs
    exact hAbs.mono
      (sup_le_sup (MeasurableSpace.comap_mono hPredLeProd) le_rfl) le_rfl
  have hAbsPath : Measurable (fun p : ℝ≥0 × ℝ =>
      ENNReal.ofReal (|HS ((p.1,ω),p.2)|)) :=
    hAbsStd.comp ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)
  let f : (ℝ≥0 × ℝ) → ℝ≥0∞ := fun p =>
    if s < p.1 ∧ p.1 ≤ t ∧ p.2 ∈ B then ENNReal.ofReal (|HS ((p.1,ω),p.2)|) else 0
  have hf : Measurable f := by
    have hcond : MeasurableSet {p : ℝ≥0 × ℝ |
        s < p.1 ∧ p.1 ≤ t ∧ p.2 ∈ B} := by
      have hfst : Measurable (fun p : ℝ≥0 × ℝ => p.1) := measurable_fst
      have hsnd : Measurable (fun p : ℝ≥0 × ℝ => p.2) := measurable_snd
      exact (measurableSet_Ioi.preimage hfst).inter
        ((measurableSet_Iic.preimage hfst).inter (hBm.preimage hsnd))
    simpa [f] using Measurable.ite hcond hAbsPath measurable_const
  let a : ℝ≥0 → ℝ≥0∞ := fun r =>
    if 0 < r ∧ J r ω ≠ 0 then f (r, J r ω) else 0
  have hout (r : ℝ≥0) (hr : r ∉ T) : a r = 0 := by
    have hn : ¬(s < r ∧ r ≤ t ∧ J r ω ∈ B) := by
      intro hx
      exact hr ((hT r).mpr hx)
    by_cases hj : 0 < r ∧ J r ω ≠ 0
    · simp [a, f, hj, hn]
    · simp [a, hj]
  have hsum : (∑' r : ℝ≥0, a r) = ∑ r ∈ T, a r :=
    tsum_eq_sum hout
  have hterm (r : ℝ≥0) (hr : r ∈ T) :
      a r = ENNReal.ofReal (|HS ((r,ω),J r ω)|) := by
    obtain ⟨hrs, hrt, hrB⟩ := (hT r).mp hr
    have hneg : J r ω < 0 := hBneg hrB
    have hj : J r ω ≠ 0 := ne_of_lt hneg
    have hpos : (0 : ℝ≥0) < r :=
      lt_of_le_of_lt (zero_le : (0 : ℝ≥0) ≤ s) hrs
    have hactive : 0 < r ∧ J r ω ≠ 0 := ⟨hpos, hj⟩
    have hband : s < r ∧ r ≤ t ∧ J r ω ∈ B := ⟨hrs, hrt, hrB⟩
    change (if 0 < r ∧ J r ω ≠ 0 then
      (if s < r ∧ r ≤ t ∧ J r ω ∈ B then
        ENNReal.ofReal (|HS ((r,ω),J r ω)|) else 0) else 0) = _
    rw [if_pos hactive, if_pos hband]
  calc
    (∫⁻ p : ℝ≥0 × ℝ,
      (if s < p.1 ∧ p.1 ≤ t ∧ p.2 ∈ B then
        ENNReal.ofReal (|HS ((p.1,ω),p.2)|) else 0) ∂NX ω) =
      ∑' r : ℝ≥0, a r := by
        simpa only [f, a, J, NX] using
          (avram_wave4_04a_actual_intrinsic_lintegral_eq_jump_sum X ω f hf)
    _ = ∑ r ∈ T, a r := hsum
    _ = ∑ r ∈ T, ENNReal.ofReal (|HS ((r,ω),J r ω)|) :=
      Finset.sum_congr rfl hterm
