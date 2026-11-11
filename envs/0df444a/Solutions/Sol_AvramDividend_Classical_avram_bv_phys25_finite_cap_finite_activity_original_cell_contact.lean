-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_phys25_finite_cap_finite_activity_original_cell_contact
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T10:26:13.754664+00:00
-- url     : https://prove2.me/submissions/90aa2f54-ecb0-4c82-9839-4e3b109e4670
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys28_finite_cap_finite_activity_signed_mean_gap
import Theorems.Thm_AvramDividend_Classical_avram_bv_phys26_original_finite_activity_exact_B_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_cash_prefix_positive_F_and_fatou
import Theorems.Thm_AvramDividend_Classical_avram_a19_uniform_delta_profile
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
/-- Source-exact signed expected gap gives an L¹-centred terminal correction. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 < T)
    (u : ℕ → ℕ → ℝ≥0)
    (hgrid : ∀ n, u n 0 = 0 ∧ ((u n (n + 1) : ℝ) = T - T / ((n : ℝ) + 2)))
    (hmono : ∀ n i, i < n + 1 → u n i ≤ u n (i + 1))
    (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2))
    (B : ℕ → Ω → ℝ)
    (hB : ∀ n ω,
      let Z : ℕ → ℝ := fun i => Function.leftLim (fun t : ℝ≥0 =>
        x + X.X t ω - rightLimit D t ω) (u n i)
      B n ω =
        (∑ i ∈ Finset.range (n + 1),
          if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
              0 < Z i ∧ ENNReal.ofReal (Z i) < C then
            Real.exp (-(q * (u n i : ℝ))) *
              (X.generator w (Z i) - q * w (Z i)) *
              ((u n (i + 1) : ℝ) - (u n i : ℝ))
          else 0) +
        (let J : ℝ≥0 → ℝ := fun t => ∑' v : ℝ≥0,
          if 0 < v ∧ v ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
          else 0
         let R : ℝ≥0 → ℝ := fun t => ((t : ℝ) * X.drift - X.X t ω) - J t
         ∑ i ∈ Finset.range (n + 1),
           (if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
               0 < Z i ∧ ENNReal.ofReal (Z i) < C then
             Real.exp (-(q * (u n i : ℝ))) * deriv w (Z i)
           else 0) * (R (u n i) - R (u n (i + 1)))))
    (hAllB : ∀ᵐ ω ∂P, ∀ n : ℕ, B n ω ≤ 0)
    (hPre : ∀ᵐ ω ∂P, ∀ n i, Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n (i + 1)) =
      riskProcess X x D (u n (i + 1)) ω)
    (hFinite : C ≠ ⊤) (hActivity : X.ν (Iio (0 : ℝ)) < ⊤) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let F : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
        else 0)
    ∃ (M ErrCell ErrContact : ℕ → ℕ → Ω → ℝ) (η : ℕ → ℝ),
      (∀ n, 0 < η n) ∧
      Tendsto η atTop (nhds (0 : ℝ)) ∧
      (∀ n k, Integrable (M n k) P ∧
        (∫ ω, M n k ω ∂P) = 0) ∧
      (∀ n k, Integrable (fun ω => max (ErrCell n k ω) 0) P) ∧
      (∀ n k, Integrable (fun ω => max (ErrContact n k ω) 0) P) ∧
      (∀ n k, ∀ᵐ ω ∂P,
        F n ω ≤ w x + (M n k ω + B n ω) +
          max (ErrCell n k ω) 0 + max (ErrContact n k ω) 0) ∧
      (∀ n (ε : ℝ), 0 < ε →
        ∃ k : ℕ,
          (∫ ω, max (ErrCell n k ω) 0 ∂P) +
            (∫ ω, max (ErrContact n k ω) 0 ∂P) ≤ η n + ε) := by
  dsimp only
  letI : IsProbabilityMeasure P := X.isProbability
  let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
  let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
  let F : ℕ → Ω → ℝ := fun n ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
    (if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
  have hBint := avram_bv_phys26_original_finite_activity_exact_B_integrable
    X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen hw_grad x hx hxc
    D hD hw_nonneg hjump T hT u hgrid hmono huniform B hB hFinite hActivity
  have hDelta := avram_a19_uniform_delta_profile T hT; dsimp only at hDelta
  obtain ⟨hδpos, hδle, hδanti, hδzero⟩ := hDelta
  have hPay := avram_p3_grid4_original_cash_prefix_positive_F_and_fatou
    X hBV x C D hD w hw_cont hw_neg q (le_of_lt hq) T hT hw_nonneg δ hδpos hδle hδanti hδzero
  dsimp only at hPay
  have hFint : ∀ n, Integrable (F n) P := fun n => (hPay.1 n).2.1
  have hGap := avram_bvb_phys28_finite_cap_finite_activity_signed_mean_gap
    X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen hw_grad x hx hxc
    D hD hw_nonneg hjump T hT u hgrid hmono huniform B hB hAllB hPre hFinite hActivity
  dsimp only at hGap
  let g : ℕ → ℝ := fun n =>
    max ((∫ ω, F n ω ∂P) - ((∫ ω, B n ω ∂P) + w x)) 0
  let η : ℕ → ℝ := fun n => g n + δ n
  have hηzero : Tendsto η atTop (𝓝 (0 : ℝ)) := by
    simpa only [η, g, δ, F, S, zero_add] using hGap.add hδzero
  have hηpos : ∀ n, 0 < η n := by
    intro n; dsimp [η, g]
    have := le_max_right ((∫ ω, F n ω ∂P) - ((∫ ω, B n ω ∂P) + w x)) (0 : ℝ)
    linarith [hδpos n]
  let M : ℕ → ℕ → Ω → ℝ := fun n _ ω => (F n ω - B n ω) - (∫ ξ, F n ξ - B n ξ ∂P)
  let E1 : ℕ → ℕ → Ω → ℝ := fun n _ _ => η n
  let E2 : ℕ → ℕ → Ω → ℝ := fun _ _ _ => 0
  refine ⟨M, E1, E2, η, hηpos, hηzero, ?_, ?_, ?_, ?_, ?_⟩
  · intro n k
    have hFB := (hFint n).sub (hBint n)
    refine ⟨hFB.sub (integrable_const _), ?_⟩
    dsimp [M]
    calc
      (∫ ω, (F n ω - B n ω) - (∫ ξ, F n ξ - B n ξ ∂P) ∂P) =
          (∫ ω, F n ω - B n ω ∂P) -
          (∫ ω, (∫ ξ, F n ξ - B n ξ ∂P) ∂P) := by
            exact integral_sub hFB (integrable_const _)
      _ = 0 := by simp
  · intro n k; simpa only [E1, max_eq_left (hηpos n).le] using
      (integrable_const (μ := P) (c := η n))
  · intro n k; simpa only [E2, max_self] using
      (integrable_const (μ := P) (c := (0 : ℝ)))
  · intro n k
    have hMean := integral_sub (hFint n) (hBint n)
    have hgap : (∫ ξ, F n ξ ∂P) - ((∫ ξ, B n ξ ∂P) + w x) ≤ η n := by
      change _ ≤ g n + δ n
      exact le_trans (le_max_left _ _) (le_add_of_nonneg_right (hδpos n).le)
    filter_upwards [] with ω
    dsimp [M, E1, E2]; rw [hMean]
    simp only [max_eq_left (hηpos n).le, max_eq_left (le_refl (0 : ℝ))]
    linarith
  · intro n ε hε; refine ⟨0, ?_⟩
    dsimp [E1, E2]
    simp only [max_eq_left (hηpos n).le, max_eq_left (le_refl (0 : ℝ))]
    simp; linarith
