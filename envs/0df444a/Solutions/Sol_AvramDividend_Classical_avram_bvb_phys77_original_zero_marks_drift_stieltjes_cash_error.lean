-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys77_original_zero_marks_drift_stieltjes_cash_error
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T07:53:14.449097+00:00
-- url     : https://prove2.me/submissions/1880ae1e-a87a-4785-a2be-c2d7fe1a7490
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys79_original_zero_marks_stopped_marked_jump_compensator
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys81_original_zero_marks_weighted_BV_grid_R_sum_zero
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys82_original_zero_marks_deterministic_stieltjes_generator_cash_bound
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology BigOperators
noncomputable section
/-- Reduce original zero-mark physical cash to deterministic Stieltjes cash. -/
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
      (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) -
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
              (X.generator w (Z i) - q * w (Z i)) * ((u n (i + 1) : ℝ) - (u n i : ℝ))
          else 0) +
        (let J : ℝ≥0 → ℝ := fun t =>
          ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω else 0
         let R : ℝ≥0 → ℝ := fun t =>
           ((t : ℝ) * X.drift - X.X t ω) - J t
         ∑ i ∈ Finset.range (n + 1),
           (if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧ 0 < Z i ∧
               ENNReal.ofReal (Z i) < C then
             Real.exp (-(q * (u n i : ℝ))) * deriv w (Z i)
           else 0) * (R (u n i) - R (u n (i + 1)))))
    (hAllB : ∀ᵐ ω ∂P, ∀ n : ℕ, B n ω ≤ 0)
    (hPre : ∀ᵐ ω ∂P, ∀ n i,
      Function.leftLim (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω)
        (u n (i + 1)) = riskProcess X x D (u n (i + 1)) ω)
    (hFinite : C ≠ ⊤)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let F : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then Real.exp (-(q * T)) *
        w (riskProcess X x D S ω) else 0)
    let U : ℝ≥0 → Ω → ℝ := fun t ω => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    let H : ℕ → (ℝ≥0 × Ω) × ℝ → ℝ := fun n p =>
      if 0 < p.1.1 ∧ (p.1.1 : ℝ) < T - δ n ∧
         (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 ∧ 0 ≤ U p.1.1 p.1.2 ∧
         ENNReal.ofReal (U p.1.1 p.1.2) ≤ C ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (U p.1.1 p.1.2 + p.2) - w (U p.1.1 p.1.2)) else 0
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {t : ℝ≥0 | 0 < t ∧ X.X t ω -
        Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0}).map
        (fun t : ℝ≥0 => (t, X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t)))
    let M : ℕ → Ω → ℝ := fun n ω =>
      (∫ p, H n ((p.1, ω), p.2) ∂(NX ω)) -
        (∫ t, ∫ z, H n ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
          ∂(((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal))
    let E : ℕ → Ω → ℝ := fun n ω => F n ω - (w x + (M n ω + B n ω))
    ∀ᵐ ω ∂P,
      (∀ t : ℝ≥0, t ≤ S → X.X t ω = (t : ℝ) * X.drift) →
      (NX ω) (Ioc (0 : ℝ≥0) S ×ˢ Iio (0 : ℝ)) = 0 →
      Tendsto (fun n => if ruinTime X x D ω = 0 then 0 else max (E n ω) 0)
        atTop (𝓝 0) := by
  intro δ S F U H NX M E
  let Z : ℕ → Ω → ℕ → ℝ := fun n ω i => Function.leftLim
    (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
  let W : ℕ → ℕ → Ω → ℝ := fun n i ω =>
    if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
        0 < Z n ω i ∧ ENNReal.ofReal (Z n ω i) < C then
      Real.exp (-(q * (u n i : ℝ))) * deriv w (Z n ω i)
    else 0
  let G : ℕ → Ω → ℝ := fun n ω =>
    ∑ i ∈ Finset.range (n + 1),
      if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
          0 < Z n ω i ∧ ENNReal.ofReal (Z n ω i) < C then
        Real.exp (-(q * (u n i : ℝ))) *
          (X.generator w (Z n ω i) - q * w (Z n ω i)) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0
  let K : ℕ → Ω → ℝ := fun n ω =>
    ∫ t, ∫ z, H n ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
      ∂(((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)
  have hBound : ∀ n i, i ≤ n + 1 → u n i ≤ S := by
    intro n i hi
    have hiR : (i : ℝ) ≤ (n : ℝ) + 2 := by exact_mod_cast (show i ≤ n + 2 by omega)
    have hn : 0 < (n : ℝ) + 2 := by positivity
    have hb : (u n i : ℝ) ≤ (S : ℝ) := by
      change (u n i : ℝ) ≤ T
      rw [huniform n i]
      apply (div_le_iff₀ hn).mpr
      nlinarith [mul_nonneg (le_of_lt hT) (sub_nonneg.mpr hiR)]
    exact_mod_cast hb
  have hRall := avram_bvb_phys81_original_zero_marks_weighted_BV_grid_R_sum_zero
    X hX hBV S u hBound W
  have hCash := avram_bvb_phys82_original_zero_marks_deterministic_stieltjes_generator_cash_bound
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump T hT
      u hgrid hmono huniform B hB hAllB hPre hFinite hActivity
  filter_upwards [hRall, hCash] with ω hRω hCashω
  intro hPath hZero
  have hRsum := hRω hZero
  have hBid : ∀ n, B n ω = G n ω := by
    intro n
    have hb := hB n ω
    have hrs := hRsum n
    dsimp only [W, Z] at hrs hb
    rw [hrs] at hb
    simpa only [add_zero] using hb
  have hδ : ∀ n, 0 ≤ δ n := by
    intro n; exact div_nonneg (le_of_lt hT) (by positivity)
  have hMid : ∀ n, M n ω = -K n ω := by
    exact avram_bvb_phys79_original_zero_marks_stopped_marked_jump_compensator
      X x D ω S δ hδ C q w U hZero
  have hEid : ∀ n, E n ω = F n ω - (w x + ((-K n ω) + G n ω)) := by
    intro n
    change F n ω - (w x + (M n ω + B n ω)) = _
    rw [hMid n, hBid n]
  simpa only [hEid] using (hCashω hPath hZero)
