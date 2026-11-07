-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid4_uniform_survival_original_caplinear_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T09:42:30.580715+00:00
-- url     : https://prove2.me/submissions/73653ced-2fc5-4804-a1bc-9bc77ac1cee3

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_surviving_strict_horizon_source_upper
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Instantiate the actual original controlled process, its strict stopped
dividend measure, and cap-linear frozen source on each uniform physical grid. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (hx : 0 ≤ x)
    (C : ℝ≥0∞) (hC : 0 < C) (hxc : ENNReal.ofReal x ≤ C)
    (w : ℝ → ℝ) (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ z : ℝ, z < 0 → w z = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (q : ℝ) (hq : 0 < q) (T : ℝ) (hT : 0 < T)
    (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i,
      (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2))
    (n : ℕ) (ω : Ω)
    (hSurvive :
      ENNReal.ofReal T < ruinTime X x D ω) :
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z
      else if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal)
    let e : ℕ → ℝ := fun i => Real.exp (-(q * (u n i : ℝ)))
    let source : ℕ → ℝ := fun i =>
      V (x + X.X (u n (i + 1)) ω - rightLimit D (u n i) ω) -
      V (x + X.X (u n i) ω - rightLimit D (u n i) ω)
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal +
      Real.exp (-(q * T)) * w (riskProcess X x D S ω) ≤
      w x + (∑ i ∈ Finset.range (n + 1), e i * source i) +
        e (n + 1) * (V (x + X.X S ω - rightLimit D (u n (n + 1)) ω) -
          V (x + X.X (u n (n + 1)) ω -
            rightLimit D (u n (n + 1)) ω)) := by
  let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
  have hS : 0 < S := by
    exact_mod_cast hT
  have hz : u n 0 = 0 := by
    apply NNReal.coe_injective
    simpa using huniform n 0
  have hGrid : ∀ i : ℕ, i < n + 1 → u n i < u n (i + 1) := by
    intro i hi
    have hr : (u n i : ℝ) < (u n (i + 1) : ℝ) := by
      rw [huniform n i, huniform n (i + 1)]
      apply div_lt_div_of_pos_right ?_ (by positivity)
      have hi' : (i : ℝ) < ((i + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.lt_succ_self i
      exact mul_lt_mul_of_pos_left hi' hT
    exact_mod_cast hr
  have hUpper : ∀ i : ℕ, i < n + 1 → u n (i + 1) ≤ S := by
    intro i hi
    have hnat : i + 1 ≤ n + 2 := by omega
    have hreal : (((i + 1 : ℕ) : ℝ)) ≤ (n : ℝ) + 2 := by exact_mod_cast hnat
    have hr : (u n (i + 1) : ℝ) ≤ T := by
      rw [huniform n (i + 1)]
      apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 2)).2
      nlinarith
    exact_mod_cast hr
  have hFinal : u n (n + 1) < S := by
    have hr : (u n (n + 1) : ℝ) < T := by
      rw [huniform n (n + 1)]
      apply (div_lt_iff₀ (by positivity : 0 < (n : ℝ) + 2)).2
      have hnat : n + 1 < n + 2 := by omega
      have hreal : (((n + 1 : ℕ) : ℝ)) < (n : ℝ) + 2 := by
        exact_mod_cast hnat
      exact mul_lt_mul_of_pos_left hreal hT
    exact_mod_cast hr
  have hEq : T.toNNReal = S := by
    apply NNReal.coe_injective
    change max T 0 = T
    exact max_eq_left (le_of_lt hT)
  have hSurviveS : (S : ℝ≥0∞) < ruinTime X x D ω := by
    change (T.toNNReal : ℝ≥0∞) < ruinTime X x D ω at hSurvive
    simpa only [hEq] using hSurvive
  exact avram_p3_grid4_original_surviving_strict_horizon_source_upper
    X x hx C hC hxc w hw0 hw_cont hw_neg hw_smooth hw_grad
    D hD hjump ω q (le_of_lt hq) S hS
    (u n) (n + 1) hz hGrid hUpper hFinal hSurviveS
