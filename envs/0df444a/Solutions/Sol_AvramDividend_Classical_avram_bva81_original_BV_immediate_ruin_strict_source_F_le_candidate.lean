-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva81_original_BV_immediate_ruin_strict_source_F_le_candidate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T21:21:12.113579+00:00
-- url     : https://prove2.me/submissions/a22d8395-ccde-4210-a8f4-099a542211c7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_immediate_ruin_strict_horizon_cash_le_candidate
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
        w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 < T)
    (hInfinite : ¬ X.ν (Iio (0 : ℝ)) < ⊤)
    (u : ℕ → ℕ → ℝ≥0)
    (hu0 : ∀ n, u n 0 = 0)
    (huniform : ∀ n i, (u n i : ℝ) =
      T * (i : ℝ) / ((n : ℝ) + 2))
    (a b : ℕ → ℝ)
    (ha : ∀ n, 0 < a n)
    (ha2 : ∀ n, a n ≤ 2)
    (hab : ∀ n, a n ≤ b n)
    (hinside : ∀ n, Icc (a n / 2) (b n) ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hcover : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ n ≥ N, y ∈ Icc (a n) (b n)) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let F : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
    ∀ m : ℕ, ∀ ω : Ω, ruinTime X x D ω = 0 → F m ω ≤ w x := by
  intro δ S F m ω hruin
  have hden : 0 < (m : ℝ) + 2 := by positivity
  have hnum : 0 < T * ((m : ℝ) + 1) := by positivity
  have hfrac : 0 < T * ((m : ℝ) + 1) / ((m : ℝ) + 2) :=
    div_pos hnum hden
  have heq : T * ((m : ℝ) + 1) / ((m : ℝ) + 2) =
      T - T / ((m : ℝ) + 2) := by
    field_simp
    ring
  have hcut : 0 < T - δ m := by
    dsimp [δ]
    linarith
  have hCash :=
    avram_p3_c_bvchain_original_immediate_ruin_strict_horizon_cash_le_candidate
      X w C hC hw0 hw_cont hw_neg hw_smooth hw_grad x hx hxc
      D hD hjump ω q (T - δ m) hcut hruin
  have hTerm : ¬ (S : ℝ≥0∞) < ruinTime X x D ω := by
    rw [hruin]
    exact not_lt.mpr bot_le
  simpa only [F, hTerm, if_false, add_zero] using hCash
