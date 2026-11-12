-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_positive_shift_original_uniform_grid_prefix_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T00:29:00.891182+00:00
-- url     : https://prove2.me/submissions/be5befb9-9efc-4b8c-ac05-29db31ec18e6

import Mathlib.Probability.Process.Filtration
import Theorems.Thm_AvramDividend_Classical_avram_chat24_original_shifted_finite_prefix_budget
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Finset AvramDividend.Classical
open scoped NNReal ENNReal Classical
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
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (hTop : C = ⊤) (δ : ℝ) (hδ : 0 < δ) :
    let S : ℝ≥0 := ⟨T, hT⟩
    let a : ℝ := min δ 1 / 2
    let b : ℝ := x + δ + T * X.drift + 1
    let τ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (S : ℝ≥0∞)).toNNReal
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => (x + δ) + X.X s p.2 - rightLimit D s p.2) p.1
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) ∧
          Y p.1 ∈ Icc a b ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (Y p.1 + p.2) - w (Y p.1)) else 0
    let μ : Measure ℝ≥0 :=
      (((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)
    ∀ ω (B : ℝ≥0), 0 < B → B ≤ S →
      (B : ℝ≥0∞) < ruinTime X x D ω → ∀ n : ℕ,
    let N : ℕ := n + 1
    let u : ℕ → ℝ≥0 := fun i => B * (i : ℝ≥0) / (N : ℝ≥0)
    let e : ℕ → ℝ := fun i => Real.exp (-(q * (u i : ℝ)))
    let U : ℕ → ℝ := fun i => riskProcess X x D (u i) ω + δ
    let Z : ℕ → ℝ := fun i => x + δ + X.X (u (i + 1)) ω - D (u i) ω
    (∑ i ∈ Finset.range N, e i * (D (u (i + 1)) ω - D (u i) ω)) + e N * w (U N) ≤
      w (x + δ) + (∑ i ∈ Finset.range N,
        ((e (i + 1) - e i) * w (U i) + e (i + 1) * (w (Z i) - w (U i)))) +
        q * ((B : ℝ) / (N : ℝ)) * D B ω := by
  classical
  intro S a b τ Y NX H μ ω B hB hBS hBruin n N u e U Z
  have hs : ContDiffOn ℝ 1 w (Ioi 0) :=
    hw_smooth.mono fun y hy => ⟨hy, by simp [hTop]⟩
  have hg (y : ℝ) (hy : 0 < y) : 1 ≤ deriv w y := hw_grad y hy (by simp [hTop])
  have hNp : 0 < (N : ℝ≥0) := by dsimp [N]; positivity
  have hu : Monotone u := by
    intro i j hij
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hij) (show 0 ≤ B from by positivity))
      (show 0 ≤ (N : ℝ≥0) from by positivity)
  have hu0 : u 0 = 0 := by simp [u]
  have huN : u N = B := by
    dsimp [u]
    exact mul_div_cancel_right₀ B (ne_of_gt hNp)
  have hwidth (i : ℕ) (hi : i < N) :
      (u (i + 1) : ℝ) - (u i : ℝ) ≤ (B : ℝ) / (N : ℝ) := by
    dsimp [u]
    push_cast
    exact le_of_eq (by ring)
  have hp := avram_chat24_original_shifted_finite_prefix_budget
    X x δ q C D hD w hs hg hδ hq.le ω u hu hu0 N ((B : ℝ) / (N : ℝ)) hwidth
    (by simpa only [huN] using hBruin)
  simpa only [e, U, Z, huN] using hp
