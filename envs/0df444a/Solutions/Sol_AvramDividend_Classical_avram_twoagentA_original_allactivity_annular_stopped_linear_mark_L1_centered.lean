-- Prove2me | solution 1 for AvramDividend.Classical.avram_twoagentA_original_allactivity_annular_stopped_linear_mark_L1_centered
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T09:22:38.894013+00:00
-- url     : https://prove2.me/submissions/4181315c-36dd-40c6-86bd-e179a1b6bafa

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_pj_reward70_original_finiteband_predictable_stopped_Campbell_L1
import Theorems.Thm_AvramDividend_Classical_avram_pj_reward71_original_compact_gradient_mark_predictable_kernel
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_negative_levy_mark_tail_finite_mass_at_every_small_threshold
import Theorems.Thm_AvramDividend_Classical_avram_pj_reward63_compact_clipped_firstorder_discounted_mark_uniform_bound
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0) (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω)) (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) → rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) - w (riskProcess X x D t ω - (rightLimit D t ω - D t ω))) (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0) (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) (hτmeas : Measurable (fun ω => (τ ω : ℝ))) (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0))) (ρ : Ω → ℝ≥0) (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0))) (hρle : ∀ ω, ρ ω ≤ τ ω) (G : Ω → ℝ) (hGdef : ∀ ω, G ω = (if ρ ω = 0 then w x else Real.exp (-(q * (ρ ω : ℝ))) * w (if (ρ ω : ℝ≥0∞) < ruinTime X x D ω then x + X.X (ρ ω) ω - rightLimit D (ρ ω) ω else riskProcess X x D (ρ ω) ω) + (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (ρ ω : ℝ), ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)) (hGI : Integrable G P) (A : Set Ω) (hA : MeasurableSet[𝓕.rightCont 0] A) (Cband u v δ η : ℝ)
    (hu : 0 < u) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (huv : u + δ < v) (hη : 0 < η) (hη1 : η < 1)
    (hv : v < Cband)     (hwCb : ContDiffOn ℝ 2 w (Ioo 0 Cband)) :
  (let T : ℝ≥0 := (n : ℝ≥0)
   let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
     (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
   let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
     ((Measure.count.restrict {s : ℝ≥0 | 0 < s ∧ X.X s ω -
       Function.leftLim (fun t : ℝ≥0 => X.X t ω) s ≠ 0}).map
       (fun s : ℝ≥0 => (s, X.X s ω -
         Function.leftLim (fun t : ℝ≥0 => X.X t ω) s)))
   let μT : Measure ℝ≥0 :=
     ((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal
   let H : Ω → (ℝ≥0 × ℝ) → ℝ := fun ω p =>
     if p.1 ≤ T ∧ p.2 ∈ Ioo (-1 : ℝ) (-η) then
       Real.exp (-(q * (p.1 : ℝ))) *
         (if Y (p.1, ω) ∈ Icc (u + δ) v then
           deriv w (Y (p.1, ω)) * p.2 else 0) else 0
   ∀ σ : Ω → ℝ≥0,
     IsStoppingTime 𝓕.rightCont (fun ω => (σ ω : WithTop ℝ≥0)) →
     Integrable (fun ω =>
       (∫ p, (if p.1 ≤ σ ω then H ω p else 0) ∂(NX ω)) -
       (∫ t, ∫ z, (if t ≤ σ ω then H ω (t,z) else 0)
         ∂(X.ν.restrict (Iio (0 : ℝ))) ∂μT)) P ∧
     (∫ ω, ((∫ p, (if p.1 ≤ σ ω then H ω p else 0) ∂(NX ω)) -
       (∫ t, ∫ z, (if t ≤ σ ω then H ω (t,z) else 0)
         ∂(X.ν.restrict (Iio (0 : ℝ))) ∂μT)) ∂P) = 0) := by
  classical
  let T : ℝ≥0 := (n : ℝ≥0)
  let Z : Set ℝ := Ioo (-1 : ℝ) (-η)
  let Y : ℝ≥0 × Ω → ℝ := fun p =>
    Function.leftLim (fun s => x + X.X s p.2 - rightLimit D s p.2) p.1
  let F : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    if p.1.1 ≤ T ∧ p.2 ∈ Z then
      Real.exp (-(q * (p.1.1 : ℝ))) *
      (if Y p.1 ∈ Icc (u + δ) v then
        deriv w (Y p.1) * p.2 else 0) else 0
  have hDZ : IsDividendStrategy 𝓕 D := hD.1.1
  have hYM : Measurable[𝓕.rightCont.predictable] Y :=
    (avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
      X x D hDZ).measurable
  have hFm : Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))] F := by
    simpa only [F, Y, Z] using
      (avram_pj_reward71_original_compact_gradient_mark_predictable_kernel
        𝓕 Y hYM w Cband u v δ η hwCb (by linarith) huv hv q T)
  have hZ : MeasurableSet Z := measurableSet_Ioo
  have hNeg : Z ⊆ Iio (0 : ℝ) := by
    intro z hz
    exact lt_trans hz.2 (neg_neg_of_pos hη)
  have hν : X.ν Z < ⊤ := by
    exact (measure_mono (fun z hz => le_of_lt hz.2)).trans_lt
      (avram_wave7_02_original_negative_levy_mark_tail_finite_mass_at_every_small_threshold
        X.ν X.ν_integrable η hη (le_of_lt hη1))
  obtain ⟨M, hM, hBound⟩ :=
    avram_pj_reward63_compact_clipped_firstorder_discounted_mark_uniform_bound
      (fun t ω => Y (t, ω)) q (le_of_lt hq)
      w Cband u v δ η hwCb (by linarith) huv hv hη
  have hFbound : ∀ p, |F p| ≤ M := by
    intro p
    by_cases h : p.1.1 ≤ T ∧ p.2 ∈ Z
    · simpa only [F, if_pos h] using hBound p.1.1 p.1.2 p.2 h.2
    · simpa [F, h] using hM
  have hFsupport : ∀ p, (T < p.1.1 ∨ p.2 ∉ Z) → F p = 0 := by
    intro p hp
    have h : ¬(p.1.1 ≤ T ∧ p.2 ∈ Z) := by
      intro h
      rcases hp with ht | hz
      · exact (not_lt_of_ge h.1) ht
      · exact hz h.2
    simp [F, h]
  dsimp only
  intro σ hσ
  have hCamp :=
    avram_pj_reward70_original_finiteband_predictable_stopped_Campbell_L1
      X T Z hZ hNeg hν F hFm hFsupport M hM hFbound σ hσ
  simpa only [F, Y, T, Z] using hCamp

