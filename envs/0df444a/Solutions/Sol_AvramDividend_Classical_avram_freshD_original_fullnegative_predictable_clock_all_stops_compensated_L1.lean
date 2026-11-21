-- Prove2me | solution 1 for AvramDividend.Classical.avram_freshD_original_fullnegative_predictable_clock_all_stops_compensated_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T19:38:15.010681+00:00
-- url     : https://prove2.me/submissions/61fdf3b0-027b-4dc2-ae7e-8d9a63051ff9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_true_Levy_finite_predictable_physical_clock
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_true_original_stopped_marked_L1_zero_mean_no_future_or_band_premises
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ)
    (H : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hHm : Measurable[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)] H)
    (hHsupport : ∀ p, (n : ℝ≥0) < p.1.1 → H p = 0)
    (hHI : ∀ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ →
      Integrable H (letI : MeasurableSpace (ℝ≥0 × Ω) :=
        𝓕.rightCont.predictable
        μ.prod (X.ν.restrict (Iio (0 : ℝ))))) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {t : ℝ≥0 |
        0 < t ∧ X.X t ω -
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) t ≠ 0}).map
        (fun t : ℝ≥0 => (t,
          X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t)))
    let μT : Measure ℝ≥0 :=
      ((volume : Measure ℝ).restrict (Icc 0 (n : ℝ))).map Real.toNNReal
    let Jρ : (Ω → ℝ≥0) → Ω → ℝ := fun ρ ω =>
      (∫ p, (if p.1 ≤ ρ ω then H ((p.1, ω), p.2) else 0) ∂(NX ω)) -
      (∫ t, ∫ z, (if t ≤ ρ ω then H ((t, ω), z) else 0)
        ∂(X.ν.restrict (Iio (0 : ℝ))) ∂μT)
    ∀ ρ : Ω → ℝ≥0,
      IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)) →
      Integrable (Jρ ρ) P ∧ (∫ ω, Jρ ρ ω ∂P) = 0 := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  intro NX μT Jρ
  let K : Ω → @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ 𝓕.rightCont.predictable
        (inferInstance : MeasurableSpace ℝ)) := fun ω =>
    @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
      (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
      (@Prod.instMeasurableSpace _ _ 𝓕.rightCont.predictable
        (inferInstance : MeasurableSpace ℝ))
      (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2)) (NX ω)
  let MK := P.bind K
  let S : Set ((ℝ≥0 × Ω) × ℝ) := {p | p.1.1 ≤ (n : ℝ≥0)}
  let MT := MK.restrict S
  obtain ⟨μ, hμ, hclock⟩ :=
    avram_pj_workerC_true_Levy_finite_predictable_physical_clock X (n : ℝ≥0)
  let N := (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
    μ.prod (X.ν.restrict (Iio (0 : ℝ))))
  have htime : Measurable[𝓕.rightCont.predictable]
      (fun p : ℝ≥0 × Ω => p.1) := by
    letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
    apply measurable_of_Ioi
    intro t
    have hs : MeasurableSet (Set.Ioi t ×ˢ (Set.univ : Set Ω)) :=
      measurableSet_predictable_Ioi_prod (𝓕 := 𝓕.rightCont)
        (i := t) MeasurableSet.univ
    simpa only [Set.prod_univ] using hs
  have ht : Measurable[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)]
      (fun p : (ℝ≥0 × Ω) × ℝ => p.1.1) :=
    htime.comp measurable_fst
  have hS : MeasurableSet[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)] S := by
    simpa only [S, Set.preimage, Set.mem_Iic] using
      (measurableSet_Iic.preimage ht)
  intro ρ hρ
  let Hρ : ((ℝ≥0 × Ω) × ℝ) → ℝ :=
    fun p => if (p.1.1 : ℝ≥0∞) ≤ (ρ p.1.2 : ℝ≥0∞) then H p else 0
  have hs : S.indicator Hρ = Hρ := by
    funext p
    by_cases ht : p.1.1 ≤ (n : ℝ≥0)
    · simp [S, Set.indicator, ht]
    · have hz := hHsupport p (lt_of_not_ge ht)
      simp [S, Set.indicator, ht, Hρ, hz]
  have hh :=
    avram_pj_workerC_true_original_stopped_marked_L1_zero_mean_no_future_or_band_premises
      X NX (by intro ω; rfl) K (by intro ω; rfl) MK rfl
      (n : ℝ≥0) S rfl hS MT N rfl μ hμ hclock rfl
      (fun ω => (ρ ω : ℝ≥0∞)) hρ H hHm (hHI μ hμ) Hρ rfl hs
  simpa only [Jρ, Hρ, μT, ENNReal.coe_le_coe,
    NNReal.coe_natCast] using hh
