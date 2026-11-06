-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid3_original_stopped_strict_prefix_zero_atom_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:23:18.250876+00:00
-- url     : https://prove2.me/submissions/363091ef-f691-4a1a-a930-cb2b08ce3f8c

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_initial_weighted_source_budget
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_uniform_physical_clock
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_strict_stopped_clock_before_ruin
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hxc : ENNReal.ofReal x ≤ C)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
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
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (T : ℝ≥0) (m n : ℕ)
    (r : ℕ → ℝ) (hr : ∀ i : ℕ, i < n → 0 ≤ r (i + 1))
    (hr0 : r 0 = 1) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → ℝ≥0 := fun k =>
      min (((min k (m + 1) : ℕ) : ℝ≥0) *
        (T / (m + 1))) τ
    u n < τ →
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z
      else if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal)
    let cash : ℕ → ℝ := fun i =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Ioc (u i : ℝ) (u (i + 1) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal
    let post : ℕ → ℝ := fun i =>
      w (x + X.X (u i) ω - rightLimit D (u i) ω)
    let source : ℕ → ℝ := fun i =>
      V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
      V (x + X.X (u i) ω - rightLimit D (u i) ω)
    rightLimit D 0 ω +
      (∑ i ∈ Finset.range n, r (i + 1) * cash i) +
        r n * post n ≤
      w x + (∑ i ∈ Finset.range n, r (i + 1) * source i) +
        ∑ i ∈ Finset.range n, (r (i + 1) - r i) * post i := by
  let τ : ℝ≥0 :=
    (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
  let u : ℕ → ℝ≥0 := fun k =>
    min (((min k (m + 1) : ℕ) : ℝ≥0) *
      (T / (m + 1))) τ
  change u n < τ → _
  intro hBefore
  let V : ℝ → ℝ := fun z =>
    if C = ⊤ then w z else
    if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal)
  have hVtop : C = ⊤ → ∀ z : ℝ, V z = w z := by
    intro htop z
    simp [V, htop]
  have hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal) := by
    intro hnot z
    simp [V, hnot]
  have hclock :=
    avram_p3_grid3_original_ruin_stopped_uniform_physical_clock
      X x D T m ω
  have hzero : u 0 = 0 := hclock.1
  have hmono : Monotone u := hclock.2.2
  have hGrid : ∀ i : ℕ, i < n → u i ≤ u (i + 1) := by
    intro i hi
    exact hmono (Nat.le_succ i)
  have hPre : ∀ i : ℕ, i < n →
      (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω := by
    intro i hi
    have hstep : u (i + 1) ≤ u n := hmono (by omega)
    exact avram_p3_grid3_original_strict_stopped_clock_before_ruin
      X x D T ω (u (i + 1)) (lt_of_le_of_lt hstep hBefore)
  exact avram_p3_c_bvchain_original_initial_weighted_source_budget
    X x C hC hxc w V hw_cont hw_smooth hw_grad
    hVtop hVfinite D hD hjump ω q hq
    u n hzero hGrid hPre r hr hr0
