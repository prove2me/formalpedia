-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys85_original_zero_marks_jump_compensator_uniform_quadrature
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T08:43:09.277284+00:00
-- url     : https://prove2.me/submissions/9f9d7c37-4177-4116-922f-92e3974f4ada

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys92_masked_original_BV_generator_drift_jump_grid_exact
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys95_original_zero_marks_one_sided_compensator_quadrature
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
/-- Exact drift/jump decomposition reduces phys85 to one-sided quadrature. -/
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
    (hgrid : ∀ n, u n 0 = 0 ∧
      ((u n (n + 1) : ℝ) = T - T / ((n : ℝ) + 2)))
    (hmono : ∀ n i, i < n + 1 → u n i ≤ u n (i + 1))
    (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2))
    (B : ℕ → Ω → ℝ)
    (hB : ∀ n ω,
      let Z : ℕ → ℝ := fun i => Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
      B n ω = (∑ i ∈ Finset.range (n + 1),
          if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
              0 < Z i ∧ ENNReal.ofReal (Z i) < C then
            Real.exp (-(q * (u n i : ℝ))) *
              (X.generator w (Z i) - q * w (Z i)) *
              ((u n (i + 1) : ℝ) - (u n i : ℝ)) else 0) +
        (let J : ℝ≥0 → ℝ := fun t =>
          ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω else 0
         let R : ℝ≥0 → ℝ := fun t => ((t : ℝ) * X.drift - X.X t ω) - J t
         ∑ i ∈ Finset.range (n + 1),
           (if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
               0 < Z i ∧ ENNReal.ofReal (Z i) < C then
             Real.exp (-(q * (u n i : ℝ))) * deriv w (Z i) else 0) *
             (R (u n i) - R (u n (i + 1)))))
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
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
    let U : ℝ≥0 → Ω → ℝ := fun t ω => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    let H : ℕ → (ℝ≥0 × Ω) × ℝ → ℝ := fun n p =>
      if 0 < p.1.1 ∧ (p.1.1 : ℝ) < T - δ n ∧
         (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 ∧
         0 ≤ U p.1.1 p.1.2 ∧ ENNReal.ofReal (U p.1.1 p.1.2) ≤ C ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (U p.1.1 p.1.2 + p.2) - w (U p.1.1 p.1.2)) else 0
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {t : ℝ≥0 | 0 < t ∧ X.X t ω -
        Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0}).map
        (fun t : ℝ≥0 => (t, X.X t ω -
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) t)))
    let G : ℕ → Ω → ℝ := fun n ω =>
      let Z : ℕ → ℝ := fun i => Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
      (∑ i ∈ Finset.range (n + 1),
          if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧ 0 < Z i ∧
              ENNReal.ofReal (Z i) < C then
            Real.exp (-(q * (u n i : ℝ))) *
              (X.generator w (Z i) - q * w (Z i)) *
              ((u n (i + 1) : ℝ) - (u n i : ℝ)) else 0)
    let K : ℕ → Ω → ℝ := fun n ω =>
      (∫ t, ∫ z, H n ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
        ∂(((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal))
    let L : ℕ → Ω → ℝ := fun n ω =>
      let Z : ℕ → ℝ := fun i => Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
      ∑ i ∈ Finset.range (n + 1),
        if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
            0 < Z i ∧ ENNReal.ofReal (Z i) < C then
          Real.exp (-(q * (u n i : ℝ))) *
            (X.drift * deriv w (Z i) - q * w (Z i)) *
            ((u n (i + 1) : ℝ) - (u n i : ℝ)) else 0
    ∀ᵐ ω ∂P,
      (∀ t : ℝ≥0, t ≤ S → X.X t ω = (t : ℝ) * X.drift) →
      (NX ω) (Ioc (0 : ℝ≥0) S ×ˢ Iio (0 : ℝ)) = 0 →
      Tendsto (fun n => if ruinTime X x D ω = 0 then 0 else
        max (L n ω - (G n ω - K n ω)) 0) atTop (𝓝 0)  := by
  intro δ S F U H NX G K L
  let J : ℕ → Ω → ℝ := fun n ω =>
    let Z : ℕ → ℝ := fun i => Function.leftLim
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
    ∑ i ∈ Finset.range (n + 1),
      if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
          0 < Z i ∧ ENNReal.ofReal (Z i) < C then
        (∫ z in Iio (0 : ℝ), Real.exp (-(q * (u n i : ℝ))) *
          (w (Z i + z) - w (Z i)) ∂X.ν) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0
  have hQuadrature := avram_bvb_phys95_original_zero_marks_one_sided_compensator_quadrature
    X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen hw_grad
    x hx hxc D hD hw_nonneg hjump T hT u hgrid hmono huniform B hB hAllB hPre hFinite hActivity
  filter_upwards [hQuadrature] with ω hω
  intro hPath hNoJump
  have hEq (n : ℕ) : G n ω = L n ω + J n ω := by
    let Z : ℕ → ℝ := fun i => Function.leftLim
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
    let A : ℕ → Prop := fun i => (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
      0 < Z i ∧ ENNReal.ofReal (Z i) < C
    have hGen : ∀ i, A i → X.GeneratorIntegrable w (Z i) := by
      intro i hi; exact (hw_gen (Z i) hi.2.1 hi.2.2).1
    have h := avram_bvb_phys92_masked_original_BV_generator_drift_jump_grid_exact X hBV w q (n + 1) A Z
      (fun i => (u n i : ℝ))
      (fun i => ((u n (i + 1) : ℝ) - (u n i : ℝ))) hGen
    simpa [G, L, J, A, Z] using h
  have hRewrite :
      (fun n => if ruinTime X x D ω = 0 then 0 else
        max (L n ω - (G n ω - K n ω)) 0) =
      (fun n => if ruinTime X x D ω = 0 then 0 else max (K n ω - J n ω) 0) := by
    funext n
    by_cases hz : ruinTime X x D ω = 0
    · simp [hz]
    · simp only [if_neg hz]
      rw [hEq n]
      congr 1
      ring
  rw [hRewrite]
  exact hω hPath hNoJump
