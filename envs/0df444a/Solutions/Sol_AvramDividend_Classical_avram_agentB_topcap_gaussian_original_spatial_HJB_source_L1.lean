-- Prove2me | solution 1 for AvramDividend.Classical.avram_agentB_topcap_gaussian_original_spatial_HJB_source_L1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T10:17:08.321913+00:00
-- url     : https://prove2.me/submissions/b7c56288-50d6-4397-843f-efd744796233
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_agentB_topcap_gaussian_prepost_centred_grid_discrepancy_L1
import Theorems.Thm_AvramDividend_Classical_avram_gledger50_original_clipped_gaussian_physical_Taylor_L1
import Theorems.Thm_AvramDividend_Classical_avram_gledger51_original_postpayment_stopped_generator_grid_nonpositive
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

/-- Transfer the original postright Gaussian Taylor plus nonpositive HJB
generator grid across the true pre/postmartingale dividend coefficient gap. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hSigmaNonzero : X.σ ≠ 0) (hNuZero : X.ν = 0) (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hTopCap : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0) (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) → rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω))) (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0))) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0))) (hρle : ∀ ω, ρ ω ≤ τ ω) (j : ℕ) (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧ riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    let H : Ω → ℝ := fun ω => if ρ ω = 0 then w x else Real.exp (-(q * (ρ ω : ℝ))) * w (riskProcess X x D (ρ ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ), ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
    let S : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (ρ ω)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      let Z : ℕ → ℝ := fun i =>
        x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
      Finset.sum (Finset.range (m + 1)) (fun i =>
        (E (v (i + 1)) - E (v i)) * w (Y (v i)) +
          E (v (i + 1)) * (w (Z i) - w (Y (v i))))
    let M : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      ∑ i ∈ Finset.range m,
          let s : ℝ≥0 := (i : ℝ≥0) * Δ
          if s < ρ ω then
            let y := riskProcess X x D s ω
            let Z := X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
            Real.exp (-(q * (s : ℝ))) *
              (deriv w y * Z +
                (iteratedDeriv 2 w y / 2) * (Z ^ 2 - (Δ : ℝ) * X.σ ^ 2))
          else 0
    (∀ m, Integrable (fun ω => max (H ω - w x - M m ω) (0 : ℝ)) P) ∧
    ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m : ℕ, k ≤ m → Integrable (fun ω => max (S m ω - M m ω) (0 : ℝ)) P ∧ (∫ ω, max (S m ω - M m ω) (0 : ℝ) ∂P) ≤ ε := by
  intro H S M
  let N : ℕ → Ω → ℝ :=  fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      ∑ i ∈ Finset.range m,
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        if s < ρ ω then
          let y := x + X.X s ω - rightLimit D s ω
          let Z := X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
          Real.exp (-(q * (s : ℝ))) *
            (deriv w y * Z +
              (iteratedDeriv 2 w y / 2) * (Z ^ 2 - (Δ : ℝ) * X.σ ^ 2))
        else 0
  let G : ℕ → Ω → ℝ := fun m ω =>
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    ∑ i ∈ Finset.range m,
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      if s < ρ ω then
        let y := x + X.X s ω - rightLimit D s ω
        (Δ : ℝ) * Real.exp (-(q * (s : ℝ))) *
          (X.generator w y - q * w y)
      else 0
  obtain ⟨hMainI, hSourceI, hDiffI, hDiffT⟩ :=
    avram_agentB_topcap_gaussian_prepost_centred_grid_discrepancy_L1 X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump n hn τ hτeq hτstop ρ hρstop hρle j hprefix
  have hTaylor :=
    avram_gledger50_original_clipped_gaussian_physical_Taylor_L1 X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop ρ hρstop hρle j hprefix
  have hDrift (m : ℕ) := avram_gledger51_original_postpayment_stopped_generator_grid_nonpositive X q w C hTopCap (fun y hy hcap => (hw_gen y hy hcap).2) x D hD.1.1 ρ j n m (Filter.Eventually.mono hprefix (fun ω hp t ht hs => (hp t ht hs).1))
  refine ⟨hMainI, ?_⟩
  intro ε hε
  obtain ⟨kt, hkt⟩ := hTaylor (ε / 2) (by linarith)
  have hNear : ∀ᶠ m : ℕ in atTop,
      (∫ ω, max (N m ω - M m ω) (0 : ℝ) ∂P) < ε / 2 :=
    hDiffT.eventually (eventually_lt_nhds (by linarith : (0 : ℝ) < ε / 2))
  obtain ⟨kd, hkd⟩ := Filter.eventually_atTop.1 hNear
  refine ⟨max kt kd, ?_⟩
  intro m hm
  have hmt : kt ≤ m := le_trans (le_max_left _ _) hm
  have hmd : kd ≤ m := le_trans (le_max_right _ _) hm
  obtain ⟨hTaylorI, hTaylorBound⟩ := hkt m hmt
  have hDiffBound := le_of_lt (hkd m hmd)
  have hNonpos : ∀ᵐ ω ∂P, G m ω ≤ 0 := by
    simpa only [G] using hDrift m
  have hPoint : ∀ᵐ ω ∂P,
      max (S m ω - M m ω) (0 : ℝ) ≤
        max (S m ω - N m ω - G m ω) (0 : ℝ) +
        max (N m ω - M m ω) (0 : ℝ) := by
    filter_upwards [hNonpos] with ω hG
    have h₁ := le_max_left (S m ω - N m ω - G m ω) (0 : ℝ); have h₂ := le_max_left (N m ω - M m ω) (0 : ℝ)
    have h₃ := le_max_right (S m ω - N m ω - G m ω) (0 : ℝ); have h₄ := le_max_right (N m ω - M m ω) (0 : ℝ)
    exact max_le (by linarith) (by linarith)
  have hTInt : Integrable (fun ω =>
      max (S m ω - N m ω - G m ω) (0 : ℝ)) P := by
    simpa only [S, N, G] using hTaylorI
  have hTBound : (∫ ω, max (S m ω - N m ω - G m ω) (0 : ℝ) ∂P) ≤ ε / 2 := by
    simpa only [S, N, G] using hTaylorBound
  have hUpperI := hTInt.add (hDiffI m)
  have hIntegral := integral_mono_ae (hSourceI m) hUpperI hPoint
  simp only [Pi.add_apply] at hIntegral
  rw [integral_add hTInt (hDiffI m)] at hIntegral
  exact ⟨hSourceI m, by linarith⟩
