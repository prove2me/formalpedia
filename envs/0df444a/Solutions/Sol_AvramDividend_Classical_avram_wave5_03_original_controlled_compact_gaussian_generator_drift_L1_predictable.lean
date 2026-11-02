-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03_original_controlled_compact_gaussian_generator_drift_L1_predictable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T14:44:12.233143+00:00
-- url     : https://prove2.me/submissions/7e5f93c1-6ef0-44db-90e7-04ce7492e799

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- The exact source prepayment reserve has an L¹ Gaussian second-derivative
generator drift on every compact C² band and every finite predictable clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo a b))
    (hau : a < u) (huv : u < v) (hvb : v < b)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    Integrable (fun p : ℝ≥0 × Ω =>
      if Y p ∈ Icc u v then X.σ ^ 2 / 2 * iteratedDeriv 2 w (Y p)
      else 0) μ := by
  classical
  have hp : IsStronglyPredictable 𝓕.rightCont
      (fun t ω => Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) :=
    avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable X x D hD
  change StronglyMeasurable[𝓕.rightCont.predictable]
    (fun p : ℝ≥0 × Ω => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) at hp
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  let G : ℝ≥0 × Ω → ℝ := fun p =>
    if Y p ∈ Icc u v then iteratedDeriv 2 w (Y p) else 0
  change Integrable (fun p : ℝ≥0 × Ω =>
    if Y p ∈ Icc u v then X.σ ^ 2 / 2 * iteratedDeriv 2 w (Y p) else 0) μ
  have hY : Measurable Y := hp.measurable
  have hcontOpen : ContinuousOn (iteratedDeriv 2 w) (Ioo a b) := by
    have hc : ContinuousOn (iteratedDerivWithin 2 w (Ioo a b)) (Ioo a b) :=
      ContDiffOn.continuousOn_iteratedDerivWithin hw
        (by norm_num) isOpen_Ioo.uniqueDiffOn
    exact hc.congr ((iteratedDerivWithin_of_isOpen isOpen_Ioo).symm)
  have hd : Measurable (fun y : ℝ =>
      if y ∈ Ioo a b then iteratedDeriv 2 w y else 0) := by
    change Measurable ((Ioo a b).piecewise (iteratedDeriv 2 w) (fun _ => (0 : ℝ)))
    exact hcontOpen.measurable_piecewise continuous_const.continuousOn
      isOpen_Ioo.measurableSet
  have hinside : Measurable (fun p : ℝ≥0 × Ω =>
      if Y p ∈ Ioo a b then iteratedDeriv 2 w (Y p) else 0) :=
    hd.comp hY
  have hband : MeasurableSet {p : ℝ≥0 × Ω | Y p ∈ Icc u v} :=
    measurableSet_Icc.preimage hY
  have hGmeas : Measurable G := by
    have heq : G = (fun p : ℝ≥0 × Ω =>
      if Y p ∈ Icc u v then
        (if Y p ∈ Ioo a b then iteratedDeriv 2 w (Y p) else 0) else 0) := by
      funext p
      change (if Y p ∈ Icc u v then iteratedDeriv 2 w (Y p) else 0) =
        (if Y p ∈ Icc u v then
          (if Y p ∈ Ioo a b then iteratedDeriv 2 w (Y p) else 0) else 0)
      by_cases hp : Y p ∈ Icc u v
      · have hp' : Y p ∈ Ioo a b :=
          ⟨lt_of_lt_of_le hau hp.1, lt_of_le_of_lt hp.2 hvb⟩
        rw [if_pos hp, if_pos hp, if_pos hp']
      · rw [if_neg hp, if_neg hp]
    rw [heq]
    exact hinside.ite hband measurable_const
  let K : Set ℝ := Icc u v
  have hKsub : K ⊆ Ioo a b := by
    intro z hz
    exact ⟨lt_of_lt_of_le hau hz.1, lt_of_le_of_lt hz.2 hvb⟩
  have hC2K : ContDiffOn ℝ 2 w K := hw.mono hKsub
  have huniqK : UniqueDiffOn ℝ K := by
    dsimp [K]
    exact uniqueDiffOn_Icc (by linarith)
  have hcontK : ContinuousOn (fun z => ‖iteratedDerivWithin 2 w K z‖) K := by
    exact (ContDiffOn.continuousOn_iteratedDerivWithin
      hC2K (by norm_num) huniqK).norm
  have hKne : K.Nonempty := by
    refine ⟨v, ?_⟩
    exact ⟨huv.le, le_rfl⟩
  obtain ⟨zM, hzM, hmax⟩ : ∃ zM ∈ K, ∀ z ∈ K,
      ‖iteratedDerivWithin 2 w K z‖ ≤ ‖iteratedDerivWithin 2 w K zM‖ :=
    isCompact_Icc.exists_isMaxOn hKne hcontK
  let M : ℝ := ‖iteratedDerivWithin 2 w K zM‖
  have hbound : ∀ p : ℝ≥0 × Ω, ‖G p‖ ≤ M := by
    intro p
    by_cases hpp : Y p ∈ K
    · have hC2 : ContDiffAt ℝ 2 w (Y p) :=
        hw.contDiffAt (isOpen_Ioo.mem_nhds (hKsub hpp))
      have heq : iteratedDerivWithin 2 w K (Y p) = iteratedDeriv 2 w (Y p) :=
        iteratedDerivWithin_eq_iteratedDeriv huniqK hC2 hpp
      have hpp' : Y p ∈ Icc u v := hpp
      change ‖if Y p ∈ Icc u v then iteratedDeriv 2 w (Y p) else 0‖ ≤ M
      rw [if_pos hpp', ← heq]
      exact hmax (Y p) hpp
    · have hpp' : Y p ∉ Icc u v := hpp
      change ‖if Y p ∈ Icc u v then iteratedDeriv 2 w (Y p) else 0‖ ≤ M
      rw [if_neg hpp', norm_zero]
      exact norm_nonneg _
  let F : ℝ≥0 × Ω → ℝ := fun p =>
    if Y p ∈ Icc u v then X.σ ^ 2 / 2 * iteratedDeriv 2 w (Y p) else 0
  have hFpoint (p : ℝ≥0 × Ω) : F p = X.σ ^ 2 / 2 * G p := by
    change (if Y p ∈ Icc u v then
      X.σ ^ 2 / 2 * iteratedDeriv 2 w (Y p) else 0) =
      X.σ ^ 2 / 2 * (if Y p ∈ Icc u v then iteratedDeriv 2 w (Y p) else 0)
    by_cases hp : Y p ∈ Icc u v
    · rw [if_pos hp, if_pos hp]
    · rw [if_neg hp, if_neg hp, mul_zero]
  have hFmeas : Measurable F := by
    have hFid : F = (fun p => X.σ ^ 2 / 2 * G p) := by
      funext p
      exact hFpoint p
    rw [hFid]
    exact measurable_const.mul hGmeas
  have hFbound (p : ℝ≥0 × Ω) : ‖F p‖ ≤ ‖X.σ ^ 2 / 2‖ * M := by
    rw [hFpoint p, norm_mul]
    exact mul_le_mul_of_nonneg_left (hbound p) (norm_nonneg _)
  letI : IsFiniteMeasure μ := ⟨hμ⟩
  change Integrable F μ
  exact Integrable.of_bound hFmeas.aestronglyMeasurable (‖X.σ ^ 2 / 2‖ * M)
    (Filter.Eventually.of_forall hFbound)
