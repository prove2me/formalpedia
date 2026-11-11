-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger18_original_topcap_physical_grid_centered
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T08:38:36.816383+00:00
-- url     : https://prove2.me/submissions/6758d506-57f3-405e-87bf-8ce7bbea0a0b

import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_avram_gledger18_original_topcap_grid_zero_cell_band
import Theorems.Thm_AvramDividend_Classical_avram_gledger18_original_topcap_predictable_C2_clipped
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_gaussian_deterministic_increment_condExp_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_gaussian_deterministic_quadratic_residual_condExp_zero
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit false
set_option pp.fullNames false
set_option pp.universes false
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : ¬ X.BoundedVariation)
  (hSigmaNonzero : X.σ ≠ 0) (hNuZero : X.ν = 0) (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hTopCap : C = ⊤) (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
  (hw_neg : ∀ y < 0, w y = 0) (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → X.GeneratorIntegrable w y
  ∧ X.generator w y - q * w y ≤ 0) (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C) (D : ℝ≥0 → Ω → ℝ) (hD :
  IsAdmissibleLe X x C D) (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω)) (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) <
  ruinTime X x D ω) → rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) - w (riskProcess X x D t ω - (rightLimit D t ω - D t ω))) (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0) (hτeq :
  ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0))) (ρ : Ω → ℝ≥0) (hρstop : IsStoppingTime
  𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0))) (hρle : ∀ ω, ρ ω ≤ τ ω) (j : ℕ) (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω → (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω
  ∧ riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) : let H : (Ω → ℝ≥0) → Ω → ℝ := fun ζ ω => if ζ ω = 0 then w x else Real.exp (-(q * (ζ ω : ℝ))) * w (riskProcess X x D (ζ ω) ω) +
  (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ζ ω : ℝ), ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal;
  ∀ m : ℕ, 0 < m →
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m
  : ℝ≥0) + 1);
    let M : Ω → ℝ := fun ω => ∑ i ∈ Finset.range m, let s : ℝ≥0 := (i : ℝ≥0) * Δ; if s < ρ ω then let y := riskProcess X x D s ω; let Z := X.X (s + Δ) ω - X.X s ω - (Δ
  : ℝ) * X.c; Real.exp (-(q * (s : ℝ))) * (deriv w y * Z + (iteratedDeriv 2 w y / 2) * (Z ^ 2 - (Δ : ℝ) * X.σ ^ 2)) else 0;
    Integrable M P ∧ (∫ ω, M ω ∂P) = 0 := by
  classical
  intro H m hm
  letI : IsProbabilityMeasure P := X.isProbability
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
  let Z : ℕ → Ω → ℝ := fun i ω =>
    X.X (s i + Δ) ω - X.X (s i) ω - (Δ : ℝ) * X.c
  let Q : ℕ → Ω → ℝ := fun i ω => Z i ω ^ 2 - (Δ : ℝ) * X.σ ^ 2
  let a : ℝ := min x ((1 : ℝ) / ((j : ℝ) + 1))
  let b : ℝ := x + ((j : ℝ) + 1)
  let interior : ℝ → Prop := fun y => 0 < y ∧ ENNReal.ofReal y < C
  let G : ℝ≥0 → Ω → ℝ := fun t ω =>
    if t < ρ ω ∧ riskProcess X x D t ω ∈ Icc a b then
      Real.exp (-(q * (t : ℝ))) *
        (if interior (riskProcess X x D t ω) then deriv w (riskProcess X x D t ω) else 0)
    else 0
  let K : ℝ≥0 → Ω → ℝ := fun t ω =>
    if t < ρ ω ∧ riskProcess X x D t ω ∈ Icc a b then
      Real.exp (-(q * (t : ℝ))) *
        (if interior (riskProcess X x D t ω) then iteratedDeriv 2 w (riskProcess X x D t ω) else 0)
    else 0
  let F : ℕ → Ω → ℝ := fun i ω =>
    G (s i) ω * Z i ω + (1 / 2 : ℝ) * (K (s i) ω * Q i ω)
  let M : Ω → ℝ := fun ω =>
    ∑ i ∈ Finset.range m,
      let t : ℝ≥0 := (i : ℝ≥0) * Δ
      if t < ρ ω then
        let y := riskProcess X x D t ω
        let V := X.X (t + Δ) ω - X.X t ω - (Δ : ℝ) * X.c
        Real.exp (-(q * (t : ℝ))) *
          (deriv w y * V + (iteratedDeriv 2 w y / 2) *
            (V ^ 2 - (Δ : ℝ) * X.σ ^ 2))
      else 0
  change Integrable M P ∧ (∫ ω, M ω ∂P) = 0
  obtain ⟨KG, KH, hKG, hKH, hClip⟩ :=
    avram_gledger18_original_topcap_predictable_C2_clipped
      X hBV hNuZero q (le_of_lt hq) w C hTopCap hw_smooth
      x hx D hD.1.1 ρ hρstop j
  have hBand :=
    avram_gledger18_original_topcap_grid_zero_cell_band
      X x hx D hD.1.1 ρ j n m hprefix
  have hWeighted (t : ℝ≥0) (A B : Ω → ℝ) (c : ℝ)
      (hA : Measurable[𝓕.rightCont t] A)
      (hBound : ∀ ω, |A ω| ≤ c)
      (hBI : Integrable B P)
      (hCE : P[B | 𝓕.rightCont t] =ᵐ[P] fun _ => (0 : ℝ)) :
      Integrable (fun ω => A ω * B ω) P ∧
        (∫ ω, A ω * B ω ∂P) = 0 := by
    have hAglobal : Measurable A := hA.mono (𝓕.rightCont.le t) le_rfl
    have hAB : Integrable (fun ω => A ω * B ω) P := by
      apply hBI.bdd_mul hAglobal.stronglyMeasurable.aestronglyMeasurable
      filter_upwards [] with ω
      simpa only [Real.norm_eq_abs] using hBound ω
    refine ⟨hAB, ?_⟩
    have hPull := condExp_mul_of_stronglyMeasurable_left
      hA.stronglyMeasurable hAB hBI
    calc
      (∫ ω, A ω * B ω ∂P) =
          (∫ ω, P[(fun ω => A ω * B ω) | 𝓕.rightCont t] ω ∂P) := by
            symm
            exact integral_condExp (𝓕.rightCont.le t)
      _ = (∫ ω, A ω * P[B | 𝓕.rightCont t] ω ∂P) :=
        integral_congr_ae hPull
      _ = (∫ ω, (0 : ℝ) ∂P) := by
        apply integral_congr_ae
        filter_upwards [hCE] with ω hω
        simp [hω]
      _ = 0 := by simp
  have hCell (i : ℕ) (hi : i ∈ Finset.range m) :
      Integrable (F i) P ∧ (∫ ω, F i ω ∂P) = 0 := by
    have ht : s i ≤ s i + Δ := le_add_of_nonneg_right bot_le
    have hZ := avram_wave6_03_original_rightCont_gaussian_deterministic_increment_condExp_zero
      X hNuZero (s i) (s i + Δ) ht
    have hQ := avram_wave6_03_original_rightCont_gaussian_deterministic_quadratic_residual_condExp_zero
      X hNuZero (s i) (s i + Δ) ht
    have hZI : Integrable (Z i) P ∧
        (P[Z i | 𝓕.rightCont (s i)] =ᵐ[P] fun _ => (0 : ℝ)) := by
      simpa only [Z, NNReal.coe_add, add_sub_cancel_left] using hZ
    have hQI : Integrable (Q i) P ∧
        (P[Q i | 𝓕.rightCont (s i)] =ᵐ[P] fun _ => (0 : ℝ)) := by
      simpa only [Q, Z, NNReal.coe_add, add_sub_cancel_left] using hQ
    have hG := hWeighted (s i) (G (s i)) (Z i) KG
      (hClip (s i)).1 (fun ω => ((hClip (s i)).2.2 ω).1) hZI.1 hZI.2
    have hK := hWeighted (s i) (K (s i)) (Q i) KH
      (hClip (s i)).2.1 (fun ω => ((hClip (s i)).2.2 ω).2) hQI.1 hQI.2
    have hKI : Integrable (fun ω => (1 / 2 : ℝ) * (K (s i) ω * Q i ω)) P :=
      hK.1.const_mul _
    refine ⟨hG.1.add hKI, ?_⟩
    change (∫ ω, G (s i) ω * Z i ω +
      (1 / 2 : ℝ) * (K (s i) ω * Q i ω) ∂P) = 0
    rw [integral_add hG.1 hKI, integral_const_mul]
    simp [hG.2, hK.2]
  have hFI : Integrable (fun ω => ∑ i ∈ Finset.range m, F i ω) P :=
    integrable_finset_sum _ (fun i hi => (hCell i hi).1)
  have hFzero : (∫ ω, ∑ i ∈ Finset.range m, F i ω ∂P) = 0 := by
    rw [integral_finset_sum _ (fun i hi => (hCell i hi).1)]
    exact Finset.sum_eq_zero (fun i hi => (hCell i hi).2)
  have ha : 0 < a := by
    dsimp [a]
    exact lt_min hx (one_div_pos.mpr (by positivity))
  have hAgree : M =ᵐ[P] (fun ω => ∑ i ∈ Finset.range m, F i ω) := by
    filter_upwards [hBand] with ω hb
    dsimp [M, F]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hs : s i < ρ ω
    · have he : s i < ρ ω ∧ riskProcess X x D (s i) ω ∈ Icc a b :=
        ⟨hs, hb i hi hs⟩
      have hinside : interior (riskProcess X x D (s i) ω) := ⟨lt_of_lt_of_le ha he.2.1, by simp [interior, hTopCap]⟩
      have hGi : G (s i) ω = Real.exp (-(q * (s i : ℝ))) * deriv w (riskProcess X x D (s i) ω) := by simp only [G, if_pos he, if_pos hinside]
      have hKi : K (s i) ω = Real.exp (-(q * (s i : ℝ))) * iteratedDeriv 2 w (riskProcess X x D (s i) ω) := by simp only [K, if_pos he, if_pos hinside]
      have hs' : (i : ℝ≥0) * Δ < ρ ω := hs
      simp only [if_pos hs']; rw [hGi, hKi]; dsimp [Z, Q, s]; ring
    · simp [G, K, s, hs]
  refine ⟨hFI.congr hAgree.symm, ?_⟩
  calc
    (∫ ω, M ω ∂P) = (∫ ω, ∑ i ∈ Finset.range m, F i ω ∂P) :=
      integral_congr_ae hAgree
    _ = 0 := hFzero
