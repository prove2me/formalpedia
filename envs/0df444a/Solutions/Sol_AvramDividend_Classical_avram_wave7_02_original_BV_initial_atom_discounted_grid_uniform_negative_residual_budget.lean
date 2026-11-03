-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_original_BV_initial_atom_discounted_grid_uniform_negative_residual_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T19:00:33.219319+00:00
-- url     : https://prove2.me/submissions/67526bc3-d2bb-450a-be17-4ad71586749c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_initial_atom_discounted_grid_negative_value_residual_budget
open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical
set_option pp.explicit false
set_option pp.fullNames false
set_option pp.universes false
noncomputable section

/-- Controlled original BV initial payment and discounted finite grid with exact uniform negative-value residual budget. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (a b L : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hbC : ENNReal.ofReal b ≤ C) (hL1 : 1 ≤ L)
    (hLip : ∀ y ∈ Icc a b, ∀ z ∈ Icc a b,
      |w y - w z| ≤ L * |y - z|)
    (q : ℝ) (hq : 0 ≤ q)
    (M : ℝ) (hM : ∀ y ∈ Icc a b, max 0 (-w y) ≤ M) :
    ∀ᵐ ω ∂P, ∀ (u : ℕ → ℝ≥0), Monotone u →
      u 0 = 0 →
      (∀ n, x + X.X (u n) ω - rightLimit D (u n) ω ∈ Icc a b) →
      ∀ n,
        rightLimit D 0 ω +
        (∑ i ∈ Finset.range n,
          Real.exp (-(q * (u (i + 1) : ℝ))) *
            (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω)) +
        Real.exp (-(q * (u n : ℝ))) *
          w (x + X.X (u n) ω - rightLimit D (u n) ω) ≤
        w x +
        (∑ i ∈ Finset.range n,
          Real.exp (-(q * (u (i + 1) : ℝ))) *
            (L * (((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift))) +
        M * (Real.exp (-(q * (u 0 : ℝ))) -
          Real.exp (-(q * (u n : ℝ)))) := by
  filter_upwards
    [avram_wave7_02_original_BV_initial_atom_discounted_grid_negative_value_residual_budget
      X hX hBV x D hD C hC w hw_cont hw_smooth hw_grad
      hjump a b L ha hab hbC hL1 hLip q hq] with ω hGrid
  intro u hu hu0 hBand n
  have hBound := hGrid u hu hu0 hBand n
  let E : ℕ → ℝ := fun i => Real.exp (-(q * (u i : ℝ)))
  have hStep : ∀ i, E (i + 1) ≤ E i := by
    intro i
    have htn : u i ≤ u (i + 1) := hu (Nat.le_succ i)
    have htr : (u i : ℝ) ≤ (u (i + 1) : ℝ) := by
      exact_mod_cast htn
    exact Real.exp_le_exp.mpr
      (neg_le_neg (mul_le_mul_of_nonneg_left htr hq))
  have hCell : ∀ i,
      (E i - E (i + 1)) *
        max 0 (-(w (x + X.X (u i) ω - rightLimit D (u i) ω))) ≤
      (E i - E (i + 1)) * M := by
    intro i
    exact mul_le_mul_of_nonneg_left
      (hM _ (hBand i)) (sub_nonneg.mpr (hStep i))
  have hTel : ∀ k : ℕ,
      (∑ i ∈ Finset.range k, (E i - E (i + 1))) = E 0 - E k := by
    intro k
    induction k with
    | zero => simp
    | succ j ih =>
        rw [Finset.sum_range_succ, ih]
        ring
  have hResidual :
      (∑ i ∈ Finset.range n, (E i - E (i + 1)) *
        max 0 (-(w (x + X.X (u i) ω - rightLimit D (u i) ω)))) ≤
      M * (E 0 - E n) := by
    calc
      _ ≤ ∑ i ∈ Finset.range n, (E i - E (i + 1)) * M :=
        Finset.sum_le_sum (fun i hi => hCell i)
      _ = M * (∑ i ∈ Finset.range n, (E i - E (i + 1))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = M * (E 0 - E n) := by rw [hTel n]
  dsimp [E] at hResidual
  exact hBound.trans (add_le_add_right hResidual _)