-- Prove2me | solution 2 for AvramDividend.Classical.avram_ubv_finite14_original_gaussian_strict_stopped_event_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T07:44:01.169394+00:00
-- url     : https://prove2.me/submissions/749fa04f-1cf1-42f9-bb0d-e0f083fd3623
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite12_positive_clock_initial_measurable
import Theorems.Thm_AvramDividend_Classical_avram_gfinite28_original_bounded_stop_masked_strict_reward_L1
import Theorems.Thm_AvramDividend_Classical_avram_p4_f12_stopped_nonnegative_clock_zero_event_measurable
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_subordinate_clock_bounded_by_horizon_and_ruin
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite14_original_gaussian_positive_clock_event_budget
import Theorems.Thm_AvramDividend_Classical_avram_ubv_jump11_initial_event_positive_clock_partition
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (σ : ℕ → Ω → ℝ≥0)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (σ k ω : WithTop ℝ≥0)))
    (hσle : ∀ k ω, σ k ω ≤ τ ω) :
    ∀ k (A : Set Ω), MeasurableSet[𝓕.rightCont 0] A →
      (∫ ω in A,
        (if σ k ω = 0 then w x else
          Real.exp (-(q * (σ k ω : ℝ))) *
            w (riskProcess X x D (σ k ω) ω) +
          (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (σ k ω : ℝ),
            ENNReal.ofReal (Real.exp (-(q * s)))
            ∂(dividendMeasure D ω)).toReal) ∂P) ≤
          w x * (P A).toReal := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  intro k A hA
  let S : Set Ω := {ω | σ k ω = 0}
  have hS : MeasurableSet[𝓕.rightCont 0] S := by
    have hp :=
      AvramDividend.Classical.avram_ubv_finite12_positive_clock_initial_measurable
        (σ k) (hσstop k)
    simpa only [S, Set.compl_setOf, not_not] using hp.compl
  have hSfull : MeasurableSet S :=
    AvramDividend.Classical.avram_p4_f12_stopped_nonnegative_clock_zero_event_measurable
      𝓕 (σ k) (hσstop k)
  let G : Ω → ℝ := fun ω => if σ k ω = 0 then w x else
    Real.exp (-(q * (σ k ω : ℝ))) * w (riskProcess X x D (σ k ω) ω) +
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (σ k ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
      ∂(dividendMeasure D ω)).toReal
  have hGI : Integrable G P := by
    dsimp [G]
    exact AvramDividend.Classical.avram_gfinite28_original_bounded_stop_masked_strict_reward_L1
      X x C hFiniteCap hxc D hD w hw_cont hw_neg q hq
      (σ k) (hσstop k) (n : ℝ≥0)
      (AvramDividend.Classical.avram_pj_workerC_subordinate_clock_bounded_by_horizon_and_ruin
        X x C D hD n hn τ (σ k) hτeq (hσle k)).1
  have hPositive :
      ∀ B : Set Ω, MeasurableSet[𝓕.rightCont 0] B →
        (∫ ω in B ∩ Sᶜ, G ω ∂P) ≤
          w x * (P (B ∩ Sᶜ)).toReal := by
    intro B hB
    have hB' :=
      AvramDividend.Classical.avram_ubv_finite14_original_gaussian_positive_clock_event_budget
        X hX hBV hν q hq w C hC hFiniteCap hw0 hw_cont hw_neg
        hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
        n hn τ hτeq hτmeas hτstop σ hσstop hσle k B hB
    have hSet : B ∩ Sᶜ = B ∩ {ω : Ω | σ k ω ≠ 0} := by
      ext ω
      simp [S]
    rw [hSet]
    convert hB' using 1
    apply integral_congr_ae
    have hb : MeasurableSet (B ∩ Sᶜ) := by
      have hT := ((𝓕.rightCont).le 0) _ (hB.inter hS.compl)
      simpa only [hSet] using hT
    filter_upwards [ae_restrict_mem hb] with ω hω
    have hnz : σ k ω ≠ 0 := by
      intro hz
      exact hω.2 hz
    simp [G, hnz]
  have hB :=
    AvramDividend.Classical.avram_ubv_jump11_initial_event_positive_clock_partition
      (𝓕.rightCont 0) ((𝓕.rightCont).le 0) S hS
      G hGI (w x) (by intro ω hω; simp [G, S] at *; simp [G, hω])
      hPositive A hA
  exact hB
