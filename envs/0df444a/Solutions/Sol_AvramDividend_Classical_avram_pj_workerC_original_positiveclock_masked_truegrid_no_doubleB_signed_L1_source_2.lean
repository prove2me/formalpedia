-- Prove2me | solution 2 for AvramDividend.Classical.avram_pj_workerC_original_positiveclock_masked_truegrid_no_doubleB_signed_L1_source
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T19:48:59.661994+00:00
-- url     : https://prove2.me/submissions/70bac11b-d7c7-4863-8465-24043e0c9acc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_masked_physmesh_ae_uniform_L2_source
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_stopped_L2_error_bound_gives_L1_convergence
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : ¬ X.BoundedVariation) (hSigmaZero : X.σ = 0) (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hCfinite : C ≠ ⊤) (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0) (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω)) (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) → rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) - w (riskProcess X x D t ω - (rightLimit D t ω - D t ω))) (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0) (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) (hτmeas : Measurable (fun ω => (τ ω : ℝ))) (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0))) (ρ : Ω → ℝ≥0) (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0))) (hρle : ∀ ω, ρ ω ≤ τ ω) (G : Ω → ℝ) (hGdef : ∀ ω, G ω = (if ρ ω = 0 then w x else Real.exp (-(q * (ρ ω : ℝ))) * w (if (ρ ω : ℝ≥0∞) < ruinTime X x D ω then x + X.X (ρ ω) ω - rightLimit D (ρ ω) ω else riskProcess X x D (ρ ω) ω) + (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (ρ ω : ℝ), ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)) (hGI : Integrable G P) (A : Set Ω) (hA : MeasurableSet[𝓕.rightCont 0] A) :
    ∀ ε : ℝ, 0 < ε →
      ∃ Cband u v δ η : ℝ,
        0 < u ∧ 0 < δ ∧ δ ≤ 1 ∧ u + δ < v ∧ 0 < η ∧ η < 1 ∧
        v < Cband ∧ v < C.toReal ∧
        ContDiffOn ℝ 2 w (Ioo 0 Cband) ∧
      (let T : ℝ≥0 := (n : ℝ≥0)
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
        (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then
          (1 : ℝ) else 0) * H p
      let GW : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p => a p.1 * HS p
      let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
        ((Measure.count.restrict {s : ℝ≥0 | 0 < s ∧ X.X s ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) s ≠ 0}).map
          (fun s : ℝ≥0 => (s, X.X s ω -
            Function.leftLim (fun t : ℝ≥0 => X.X t ω) s)))
      let μT : Measure ℝ≥0 :=
        ((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal
      let J : (Ω → ℝ≥0) → Ω → ℝ := fun ρ ω =>
        (∫ p, (if p.1 ≤ ρ ω then GW ((p.1, ω), p.2) else 0) ∂(NX ω)) -
        (∫ t, ∫ z,
          (if t ≤ ρ ω then GW ((t, ω), z) else 0)
          ∂(X.ν.restrict (Iio (0 : ℝ))) ∂μT)
      let R : ℝ≥0 × Ω → ℝ := fun p =>
        Real.exp (-(q * (p.1 : ℝ))) *
          ((if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then (1 : ℝ) else 0) *
            (if Y p ∈ Icc (u + δ) v then
              X.generator w (Y p) - q * w (Y p) else 0))
      let B : (Ω → ℝ≥0) → Ω → ℝ := fun σ ω =>
        ∫ t : ℝ≥0, if t ≤ σ ω then R (t, ω) else 0 ∂μT
      let L : Ω → ℝ := fun ω =>
        (∫ p, (if p.1 ≤ ρ ω ∧ p.2 ∈ Ioo (-1 : ℝ) (-η) then
          Real.exp (-(q * (p.1 : ℝ))) * (if Y (p.1, ω) ∈ Icc (u + δ) v then
              deriv w (Y (p.1, ω)) * p.2 else 0) else 0) ∂(NX ω)) -
        (∫ t, ∫ z, (if t ≤ ρ ω ∧ z ∈ Ioo (-1 : ℝ) (-η) then Real.exp (-(q * (t : ℝ))) * (if Y (t, ω) ∈ Icc (u + δ) v then
                deriv w (Y (t, ω)) * z else 0) else 0) ∂(X.ν.restrict (Iio (0 : ℝ))) ∂μT)
      let U : Ω → ℝ := fun ω => w x + (J ρ ω + B ρ ω + L ω)
      let V : Ω → ℝ := fun ω => Real.exp (-(q * (ρ ω : ℝ))) *
          w (riskProcess X x D (ρ ω) ω) + (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ), ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
      let A : ℕ → Ω → Finset ℝ≥0 := fun k ω =>
        ((Finset.range (k + 1)).image (fun i : ℕ => min ((i : ℝ≥0) * ((n : ℝ≥0) / ((k + 1 : ℕ) : ℝ≥0))) (ρ ω))).filter (fun t : ℝ≥0 => t = 0 ∨ t < ρ ω)
      let Q : ℕ → Ω → ℝ := fun k ω => if ρ ω = 0 then 0 else ∑ t ∈ A k ω, Real.exp (-(q * (t : ℝ))) *
          ((rightLimit D t ω - D t ω) - (w (riskProcess X x D t ω) - w (riskProcess X x D t ω - (rightLimit D t ω - D t ω))))
      ∃ (K : Ω → ℝ),
        Integrable K P ∧
        (∫ ω, |K ω| ∂P) ≤ ε / 4 ∧
        (∀ k : ℕ, Integrable (fun ω => V ω - U ω - K ω - Q k ω) P) ∧
        Tendsto (fun k : ℕ =>
          ∫ ω, |V ω - U ω - K ω - Q k ω| ∂P)
          Filter.atTop (𝓝 (0 : ℝ))) := by
  intro ε hε
  obtain ⟨Cband, u, v, δ, η, hu, hδ, hδone, huv,
    hη, hηone, hv, hvCap, hwband, hSource⟩ :=
    avram_pj_workerC_original_masked_physmesh_ae_uniform_L2_source
      X hX hBV hSigmaZero q hq w C hC hCfinite hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump n hn
      τ hτeq hτmeas hτstop ρ hρstop hρle G hGdef hGI A hA ε hε
  refine ⟨Cband, u, v, δ, η, hu, hδ, hδone, huv,
    hη, hηone, hv, hvCap, hwband, ?_⟩
  dsimp only at hSource ⊢
  obtain ⟨K, hKI, hKsmall, hEI, E, hEdef, M, hM0, hL2, hAE⟩ := hSource
  letI : IsProbabilityMeasure P := X.isProbability
  have hEI' : ∀ k, Integrable (E k) P := by
    intro k
    convert hEI k using 1
    funext ω
    exact hEdef k ω
  have hMeas : ∀ k, AEStronglyMeasurable
      (fun ω => ‖E k ω - (0 : ℝ)‖) P := by
    intro k
    simpa only [sub_zero, Real.norm_eq_abs] using
      (hEI' k).abs.aestronglyMeasurable
  have hSq : ∀ k, Integrable (fun ω => (‖E k ω - (0 : ℝ)‖)^2) P ∧
      (∫ ω, (‖E k ω - (0 : ℝ)‖)^2 ∂P) ≤ M := by
    intro k
    simpa only [sub_zero, Real.norm_eq_abs] using hL2 k
  have hAs : ∀ᵐ ω ∂P,
      Tendsto (fun k => E k ω) atTop (𝓝 ((fun _ : Ω => (0 : ℝ)) ω)) := by
    simpa only using hAE
  have hCon :=
    avram_p4_e_localise_original_stopped_L2_error_bound_gives_L1_convergence
      X E (fun _ => (0 : ℝ)) hMeas hAs M hM0 hSq
  refine ⟨K, hKI, hKsmall, hEI, ?_⟩
  simpa only [sub_zero, Real.norm_eq_abs, hEdef] using hCon
