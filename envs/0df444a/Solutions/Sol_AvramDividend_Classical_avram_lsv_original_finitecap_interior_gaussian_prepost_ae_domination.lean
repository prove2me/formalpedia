-- Prove2me | solution 1 for AvramDividend.Classical.avram_lsv_original_finitecap_interior_gaussian_prepost_ae_domination
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T22:56:17.435799+00:00
-- url     : https://prove2.me/submissions/2f7f58fe-abd2-4087-9115-fce9894c6443

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ubv_strict_C2_interior_isOpen
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ubv_C2_compact_band_gradient_lipschitz_exists
import Theorems.Thm_AvramDividend_Classical_avram_lsv_original_prefix_positive_and_rightpost_pair_band_including_zero
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hSigmaNonzero : X.σ ≠ 0)
    (hNuZero : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) -
        w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0))) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0))) (hρle : ∀ ω, ρ ω ≤ τ ω)
    (j : ℕ) (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1))
    (hpost : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t < ρ ω →
      x + X.X t ω - rightLimit D t ω ∈
        Icc ((1 : ℝ) / ((j : ℝ) + 1)) (x + ((j : ℝ) + 1)))
    (hBandCap : ENNReal.ofReal (x + ((j : ℝ) + 1)) < C) :
    let Elinear : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      ∑ i ∈ Finset.range m,
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        let Z := X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
        |if s < ρ ω then Real.exp (-(q * (s : ℝ))) else 0| *
          |deriv w (x + X.X s ω - rightLimit D s ω) -
            deriv w (riskProcess X x D s ω)| * |Z|
    let V : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      ∑ i ∈ Finset.range m,
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        let Z : ℝ := X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
        (if s < ρ ω then
          Real.exp (-(q * (s : ℝ))) * (rightLimit D s ω - D s ω) else 0) * |Z|
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ᵐ ω ∂P, ∀ m : ℕ,
        0 ≤ Elinear m ω ∧ Elinear m ω ≤ L * V m ω := by
  classical
  intro Elinear V
  let a : ℝ := (1 : ℝ) / ((j : ℝ) + 1); let b : ℝ := x + ((j : ℝ) + 1)
  have ha : 0 < a := by dsimp [a]; positivity
  have hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by
    intro y hy; exact ⟨lt_of_lt_of_le ha hy.1,
      lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hy.2) hBandCap⟩
  obtain ⟨K,hLip⟩ :=
    avram_p4_a_gaussian_ubv_C2_compact_band_gradient_lipschitz_exists
      C w hw_smooth a b
      (avram_p4_a_gaussian_ubv_strict_C2_interior_isOpen C) hBand
  refine ⟨(K : ℝ), NNReal.coe_nonneg _, ?_⟩
  have hPreBand : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      riskProcess X x D t ω ∈ Icc a b :=
    hprefix.mono (fun ω hω t ht htρ => hω t ht htρ)
  have hPair :=
    avram_lsv_original_prefix_positive_and_rightpost_pair_band_including_zero
      X x D hD.1.1 ρ a b (by
        dsimp [b]; linarith [show (0 : ℝ) ≤ (j : ℝ) from Nat.cast_nonneg _])
      hPreBand hpost
  filter_upwards [hPair] with ω hp
  intro m; constructor
  · dsimp [Elinear]; exact Finset.sum_nonneg (fun i hi => by positivity)
  · dsimp [Elinear,V]; rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi; let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℝ≥0 := (i : ℝ≥0) * Δ
    let Z : ℝ := X.X (s+Δ) ω - X.X s ω - (Δ : ℝ) * X.c
    let pre : ℝ := riskProcess X x D s ω
    let post : ℝ := x + X.X s ω - rightLimit D s ω
    let pay : ℝ := rightLimit D s ω - D s ω
    have hpay : 0 ≤ pay := sub_nonneg.mpr (dividendStrategy_le_rightLimit D hD.1.1 ω s)
    change |(if s < ρ ω then Real.exp (-(q * (s : ℝ))) else 0)| *
      |deriv w post - deriv w pre| * |Z| ≤
      (K : ℝ) * ((if s < ρ ω then Real.exp (-(q * (s : ℝ))) * pay
        else 0) * |Z|)
    by_cases hs : s < ρ ω
    · have hPost : post ∈ Icc a b := (hp s hs).2
      have hPre : pre ∈ Icc a b := (hp s hs).1
      have hdiff : |post - pre| = pay := by
        have heq : post - pre = -pay := by dsimp [post,pre,pay,riskProcess]; ring
        rw [heq,abs_neg,abs_of_nonneg hpay]
      have hL := hLip post hPost pre hPre; rw [hdiff] at hL
      simp only [if_pos hs, abs_of_nonneg (Real.exp_nonneg _)]
      calc
        Real.exp (-(q * (s:ℝ))) * |deriv w post - deriv w pre| * |Z| ≤
          Real.exp (-(q * (s:ℝ))) * ((K:ℝ) * pay) * |Z| :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hL (Real.exp_nonneg _)) (abs_nonneg _)
        _ = (K:ℝ) * (Real.exp (-(q * (s:ℝ))) * pay * |Z|) := by ring
    · simp [hs]
