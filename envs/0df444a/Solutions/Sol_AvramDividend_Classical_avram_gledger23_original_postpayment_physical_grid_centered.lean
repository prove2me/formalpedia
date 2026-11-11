-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger23_original_postpayment_physical_grid_centered
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T15:41:33.093528+00:00
-- url     : https://prove2.me/submissions/3076154c-65f2-4a8f-8671-d1b349be5914

import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_avram_gledger23_original_postpayment_clipped_C2_coefficients
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_gaussian_deterministic_increment_condExp_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_gaussian_deterministic_quadratic_residual_condExp_zero
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- The exact original postpayment coefficients, clipped at an actual
    compact band before the true stopped clock, centre each Gaussian cell. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hTopCap : C = ⊤)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (x : ℝ) (hx : 0 < x)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (j n m : ℕ) :
    let a := min x ((1 : ℝ) / ((j : ℝ) + 1))
    let b := x + ((j : ℝ) + 1)
    let Y : ℝ≥0 → Ω → ℝ := fun t ω => x + X.X t ω - rightLimit D t ω
    let interior : ℝ → Prop := fun y => 0 < y ∧ ENNReal.ofReal y < C
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let M : Ω → ℝ := fun ω => ∑ i ∈ Finset.range m,
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      if s < ρ ω ∧ Y s ω ∈ Icc a b then
        let z := X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
        Real.exp (-(q * (s : ℝ))) *
          ((if interior (Y s ω) then deriv w (Y s ω) else 0) * z +
            ((if interior (Y s ω) then iteratedDeriv 2 w (Y s ω) else 0) / 2) *
              (z ^ 2 - (Δ : ℝ) * X.σ ^ 2))
      else 0
    Integrable M P ∧ (∫ ω, M ω ∂P) = 0 := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let a := min x ((1 : ℝ) / ((j : ℝ) + 1))
  let b := x + ((j : ℝ) + 1)
  let Y : ℝ≥0 → Ω → ℝ := fun t ω => x + X.X t ω - rightLimit D t ω
  let interior : ℝ → Prop := fun y => 0 < y ∧ ENNReal.ofReal y < C
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
  let Z : ℕ → Ω → ℝ := fun i ω => X.X (s i + Δ) ω - X.X (s i) ω - (Δ : ℝ) * X.c
  let Q : ℕ → Ω → ℝ := fun i ω => Z i ω ^ 2 - (Δ : ℝ) * X.σ ^ 2
  let G : ℝ≥0 → Ω → ℝ := fun t ω =>
    if t < ρ ω ∧ Y t ω ∈ Icc a b then
      Real.exp (-(q * (t : ℝ))) *
        (if interior (Y t ω) then deriv w (Y t ω) else 0)
    else 0
  let K : ℝ≥0 → Ω → ℝ := fun t ω =>
    if t < ρ ω ∧ Y t ω ∈ Icc a b then
      Real.exp (-(q * (t : ℝ))) *
        (if interior (Y t ω) then iteratedDeriv 2 w (Y t ω) else 0)
    else 0
  let F : ℕ → Ω → ℝ := fun i ω =>
    G (s i) ω * Z i ω + (1 / 2 : ℝ) * (K (s i) ω * Q i ω)
  let M : Ω → ℝ := fun ω => ∑ i ∈ Finset.range m,
    let t : ℝ≥0 := (i : ℝ≥0) * Δ
    if t < ρ ω ∧ Y t ω ∈ Icc a b then
      let z := X.X (t + Δ) ω - X.X t ω - (Δ : ℝ) * X.c
      Real.exp (-(q * (t : ℝ))) *
        ((if interior (Y t ω) then deriv w (Y t ω) else 0) * z +
          ((if interior (Y t ω) then iteratedDeriv 2 w (Y t ω) else 0) / 2) *
            (z ^ 2 - (Δ : ℝ) * X.σ ^ 2))
    else 0
  change Integrable M P ∧ (∫ ω, M ω ∂P) = 0
  obtain ⟨KG, KH, hKG, hKH, hClip⟩ :=
    avram_gledger23_original_postpayment_clipped_C2_coefficients
      X hBV hν q hq w C hTopCap hw x hx D hD ρ hρstop j
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
      X hν (s i) (s i + Δ) ht
    have hQ := avram_wave6_03_original_rightCont_gaussian_deterministic_quadratic_residual_condExp_zero
      X hν (s i) (s i + Δ) ht
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
    have hKI : Integrable (fun ω => (1 / 2 : ℝ) * (K (s i) ω * Q i ω)) P := hK.1.const_mul _
    refine ⟨hG.1.add hKI, ?_⟩
    change (∫ ω, G (s i) ω * Z i ω +
      (1 / 2 : ℝ) * (K (s i) ω * Q i ω) ∂P) = 0
    rw [integral_add hG.1 hKI, integral_const_mul]
    simp [hG.2, hK.2]
  have hFI : Integrable (fun ω => ∑ i ∈ Finset.range m, F i ω) P := integrable_finset_sum _ (fun i hi => (hCell i hi).1)
  have hFzero : (∫ ω, ∑ i ∈ Finset.range m, F i ω ∂P) = 0 := by
    rw [integral_finset_sum _ (fun i hi => (hCell i hi).1)]
    exact Finset.sum_eq_zero (fun i hi => (hCell i hi).2)
  have hAgree : M = (fun ω => ∑ i ∈ Finset.range m, F i ω) := by
    funext ω
    dsimp only [M]
    apply Finset.sum_congr rfl
    intro i hi
    let t := s i
    let e := Real.exp (-(q * (t : ℝ)))
    let d₁ := if interior (Y t ω) then deriv w (Y t ω) else 0
    let d₂ := if interior (Y t ω) then iteratedDeriv 2 w (Y t ω) else 0
    change (if t < ρ ω ∧ Y t ω ∈ Icc a b then
      e * (d₁ * Z i ω + (d₂ / 2) * Q i ω) else 0) =
      (if t < ρ ω ∧ Y t ω ∈ Icc a b then e * d₁ else 0) * Z i ω +
      (1 / 2 : ℝ) * ((if t < ρ ω ∧ Y t ω ∈ Icc a b then e * d₂ else 0) * Q i ω)
    split_ifs <;> ring
  rw [hAgree]
  exact ⟨hFI, hFzero⟩
