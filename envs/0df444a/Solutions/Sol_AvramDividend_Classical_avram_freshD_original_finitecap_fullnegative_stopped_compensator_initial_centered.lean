-- Prove2me | solution 1 for AvramDividend.Classical.avram_freshD_original_finitecap_fullnegative_stopped_compensator_initial_centered
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T08:11:52.617072+00:00
-- url     : https://prove2.me/submissions/c0ed59fd-6f43-45b0-816e-90705874a062

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_freshD_original_stopped_closedcap_fullnegative_kernel_predictable
import Theorems.Thm_AvramDividend_Classical_avram_freshD_finite_activity_original_closedcap_discounted_negative_mark_integrable
import Theorems.Thm_AvramDividend_Classical_avram_freshD_original_fullnegative_predictable_clock_all_stops_compensated_L1
import Theorems.Thm_AvramDividend_Classical_avram_ubv_jump12_original_initial_event_compensated_clock_centering
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (hq : 0 ≤ q) (C : ℝ≥0∞) (hCfinite : C ≠ ⊤)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ) (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (hσbound : ∀ ω, σ ω ≤ (n : ℝ≥0))
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    let Y : ℝ≥0 × Ω → ℝ := fun p =>
      Function.leftLim
        (fun r : ℝ≥0 => x + X.X r p.2 - rightLimit D r p.2) p.1
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {t : ℝ≥0 |
        0 < t ∧ X.X t ω -
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) t ≠ 0}).map
        (fun t : ℝ≥0 => (t,
          X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t)))
    let μT : Measure ℝ≥0 :=
      ((volume : Measure ℝ).restrict (Icc 0 (n : ℝ))).map Real.toNNReal
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if 0 < p.1.1 ∧ p.1.1 ≤ σ p.1.2 ∧
          (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 ∧
          0 ≤ Y p.1 ∧ ENNReal.ofReal (Y p.1) ≤ C ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (Y p.1 + p.2) - w (Y p.1))
      else 0
    let J : Ω → ℝ := fun ω =>
      (∫ p, H ((p.1, ω), p.2) ∂(NX ω)) -
      (∫ t, ∫ z, H ((t, ω), z)
        ∂(X.ν.restrict (Iio (0 : ℝ))) ∂μT)
    Integrable J P ∧
      ∀ (A : Set Ω), MeasurableSet[𝓕.rightCont 0] A →
        (∫ ω in A, J ω ∂P) = 0 := by
  classical
  intro Y NX μT H J
  have hm : Measurable[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)] H := by
    simpa only [Y, NX, μT, H] using
      (avram_freshD_original_stopped_closedcap_fullnegative_kernel_predictable
        X x q hq C w hw_cont hw_neg D hD n σ hσstop hσbound)
  have hi : ∀ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ → Integrable H
        (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
         μ.prod (X.ν.restrict (Iio (0 : ℝ)))) := by
    intro μ hμ
    exact avram_freshD_finite_activity_original_closedcap_discounted_negative_mark_integrable
      X C hCfinite w hw_cont hw_neg hFinite μ hμ q hq Y σ
      (ruinTime X x D) H (by intro p; rfl) hm
  have hout : ∀ p : (ℝ≥0 × Ω) × ℝ,
      (n : ℝ≥0) < p.1.1 → H p = 0 := by
    intro p ht
    have h : ¬ p.1.1 ≤ σ p.1.2 := not_le.mpr (lt_of_le_of_lt (hσbound _) ht)
    simp [H, h]
  let Jρ : (Ω → ℝ≥0) → Ω → ℝ := fun ρ ω =>
    (∫ p, (if p.1 ≤ ρ ω then H ((p.1, ω), p.2) else 0) ∂(NX ω)) -
    (∫ t, ∫ z, (if t ≤ ρ ω then H ((t, ω), z) else 0)
      ∂(X.ν.restrict (Iio (0 : ℝ))) ∂μT)
  have hall : ∀ ρ : Ω → ℝ≥0,
      IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)) →
      Integrable (Jρ ρ) P ∧ (∫ ω, Jρ ρ ω ∂P) = 0 := by
    simpa only [Jρ, NX, μT] using
      avram_freshD_original_fullnegative_predictable_clock_all_stops_compensated_L1
        X n H hm hout hi
  have heq : ∀ ω, Jρ σ ω = J ω := by
    intro ω
    have hmask : ∀ t : ℝ≥0, ∀ z : ℝ,
        (if t ≤ σ ω then H ((t, ω), z) else 0) = H ((t, ω), z) := by
      intro t z
      by_cases ht : t ≤ σ ω
      · simp [ht]
      · have hz : H ((t, ω), z) = 0 := by simp [H, ht]
        simp [ht, hz]
    simp only [Jρ, J]
    congr 1
    · exact integral_congr_ae (Filter.Eventually.of_forall
        (fun p => hmask p.1 p.2))
    · apply integral_congr_ae
      filter_upwards [] with t
      exact integral_congr_ae (Filter.Eventually.of_forall (hmask t))
  have hj : Integrable J P := by
    have hfn : (fun ω => Jρ σ ω) = J := funext heq
    rw [← hfn]
    exact (hall σ hσstop).1
  refine ⟨hj, ?_⟩
  intro A hA
  have ha :=
    avram_ubv_jump12_original_initial_event_compensated_clock_centering
      X (n : ℝ≥0) A hA σ hσstop
      (fun ω p => H ((p.1, ω), p.2))
      (by
        intro ρ hρ
        simpa only [Jρ, NX, μT, NNReal.coe_natCast] using hall ρ hρ)
  have hσ : (∫ ω in A, Jρ σ ω ∂P) = 0 := by
    simpa only [Jρ, NX, μT, NNReal.coe_natCast] using ha
  simpa only [heq] using hσ
