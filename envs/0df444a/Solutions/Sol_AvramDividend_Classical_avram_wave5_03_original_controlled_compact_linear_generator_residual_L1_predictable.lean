-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03_original_controlled_compact_linear_generator_residual_L1_predictable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T15:14:34.133203+00:00
-- url     : https://prove2.me/submissions/113be58f-ff6b-44d2-9d49-e6f98b9d250f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_controlled_prejump_gradient_compact_band_L2_energy
import Theorems.Thm_AvramDividend_Classical_derivative_abs_le_on_compact_interior_interval

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- Original predictable c w' - q w drift has a finite first absolute moment
under genuine compact localisation and no global boundary smoothness. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo a b))
    (hau : a < u) (huv : u < v) (hvb : v < b)
    (q : ℝ)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    Integrable (fun p : ℝ≥0 × Ω =>
      if Y p ∈ Icc u v then X.c * deriv w (Y p) - q * w (Y p)
      else 0) μ := by
  classical
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  let Gd : ℝ≥0 × Ω → ℝ := fun p =>
    if Y p ∈ Icc u v then deriv w (Y p) else 0
  let Gw : ℝ≥0 × Ω → ℝ := fun p =>
    if Y p ∈ Icc u v then w (Y p) else 0
  change Integrable (fun p : ℝ≥0 × Ω =>
    if Y p ∈ Icc u v then X.c * deriv w (Y p) - q * w (Y p) else 0) μ
  have hp : IsStronglyPredictable 𝓕.rightCont
      (fun t ω => Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) :=
    avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable X x D hD
  change StronglyMeasurable[𝓕.rightCont.predictable]
    (fun p : ℝ≥0 × Ω => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) at hp
  have hY : Measurable Y := hp.measurable
  have hGdMeas : Measurable Gd := by
    simpa only [Gd, Y] using
      (avram_wave4_04b_controlled_prejump_gradient_compact_band_L2_energy
        X x D hD w a b u v hw hau huv.le hvb μ hμ).1
  have hwd : Measurable (fun y : ℝ => if y ∈ Ioo a b then w y else 0) := by
    change Measurable ((Ioo a b).piecewise w (fun _ => (0 : ℝ)))
    exact hw.continuousOn.measurable_piecewise continuous_const.continuousOn
      isOpen_Ioo.measurableSet
  have hinside : Measurable (fun p : ℝ≥0 × Ω =>
      if Y p ∈ Ioo a b then w (Y p) else 0) := hwd.comp hY
  have hband : MeasurableSet {p : ℝ≥0 × Ω | Y p ∈ Icc u v} :=
    measurableSet_Icc.preimage hY
  have hGwMeas : Measurable Gw := by
    have heq : Gw = (fun p : ℝ≥0 × Ω =>
      if Y p ∈ Icc u v then
        (if Y p ∈ Ioo a b then w (Y p) else 0) else 0) := by
      funext p
      change (if Y p ∈ Icc u v then w (Y p) else 0) =
        (if Y p ∈ Icc u v then
          (if Y p ∈ Ioo a b then w (Y p) else 0) else 0)
      by_cases hp : Y p ∈ Icc u v
      · have hp' : Y p ∈ Ioo a b :=
          ⟨lt_of_lt_of_le hau hp.1, lt_of_le_of_lt hp.2 hvb⟩
        rw [if_pos hp, if_pos hp, if_pos hp']
      · rw [if_neg hp, if_neg hp]
    rw [heq]
    exact hinside.ite hband measurable_const
  obtain ⟨Md, hMd, hderiv⟩ :=
    derivative_abs_le_on_compact_interior_interval
      w a b u v (hw.of_le (by norm_num)) hau huv.le hvb
  have hboundD : ∀ p : ℝ≥0 × Ω, ‖Gd p‖ ≤ Md := by
    intro p
    change ‖if Y p ∈ Icc u v then deriv w (Y p) else 0‖ ≤ Md
    by_cases hpp : Y p ∈ Icc u v
    · rw [if_pos hpp]
      simpa only [Real.norm_eq_abs] using hderiv (Y p) hpp.1 hpp.2
    · rw [if_neg hpp, norm_zero]
      exact hMd
  let K : Set ℝ := Icc u v
  have hKsub : K ⊆ Ioo a b := by
    intro z hz
    exact ⟨lt_of_lt_of_le hau hz.1, lt_of_le_of_lt hz.2 hvb⟩
  have hcontK : ContinuousOn (fun z => ‖w z‖) K :=
    (hw.continuousOn.mono hKsub).norm
  have hKne : K.Nonempty := ⟨v, huv.le, le_rfl⟩
  obtain ⟨zM, hzM, hmax⟩ : ∃ zM ∈ K, ∀ z ∈ K,
      ‖w z‖ ≤ ‖w zM‖ := isCompact_Icc.exists_isMaxOn hKne hcontK
  let Mw : ℝ := ‖w zM‖
  have hboundW : ∀ p : ℝ≥0 × Ω, ‖Gw p‖ ≤ Mw := by
    intro p
    change ‖if Y p ∈ Icc u v then w (Y p) else 0‖ ≤ Mw
    by_cases hpp : Y p ∈ K
    · have hpp' : Y p ∈ Icc u v := hpp
      rw [if_pos hpp']
      exact hmax (Y p) hpp
    · have hpp' : Y p ∉ Icc u v := hpp
      rw [if_neg hpp', norm_zero]
      exact norm_nonneg _
  letI : IsFiniteMeasure μ := ⟨hμ⟩
  have hIntD : Integrable Gd μ :=
    Integrable.of_bound hGdMeas.aestronglyMeasurable Md
      (Filter.Eventually.of_forall hboundD)
  have hIntW : Integrable Gw μ :=
    Integrable.of_bound hGwMeas.aestronglyMeasurable Mw
      (Filter.Eventually.of_forall hboundW)
  have hInt := (hIntD.const_mul X.c).sub (hIntW.const_mul q)
  have heq :
      (fun p : ℝ≥0 × Ω =>
        if Y p ∈ Icc u v then X.c * deriv w (Y p) - q * w (Y p) else 0) =
      (fun p : ℝ≥0 × Ω => X.c * Gd p - q * Gw p) := by
    funext p
    change (if Y p ∈ Icc u v then X.c * deriv w (Y p) - q * w (Y p) else 0) =
      X.c * (if Y p ∈ Icc u v then deriv w (Y p) else 0) -
        q * (if Y p ∈ Icc u v then w (Y p) else 0)
    by_cases hpp : Y p ∈ Icc u v
    · rw [if_pos hpp, if_pos hpp, if_pos hpp]
    · rw [if_neg hpp, if_neg hpp, if_neg hpp]
      ring
  rw [heq]
  exact hInt
