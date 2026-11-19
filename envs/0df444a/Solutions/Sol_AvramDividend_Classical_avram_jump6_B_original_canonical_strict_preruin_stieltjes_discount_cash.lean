-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_original_canonical_strict_preruin_stieltjes_discount_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T20:36:21.297408+00:00
-- url     : https://prove2.me/submissions/639babc2-178f-430b-bbfe-a4950bf0f9d3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_strict_preruin_paymentTimes_clipped_stieltjes_grid_budget
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_canonical_NNReal_grid_exact_mesh_width_and_limit
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_canonical_grid_reaches_bounded_clock_every_mesh
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (q : ℝ) (hq : 0 ≤ q) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (τ : Ω → ℝ≥0) (T : ℝ≥0)
    (hτT : τ ω ≤ T)
    (hStrict : (τ ω : ℝ≥0∞) < ruinTime X x D ω)
    (n : ℕ) (hn : τ ω ≤ (n : ℝ≥0)) :
    let u : ℕ → ℕ → ℝ≥0 := fun j i =>
      (i : ℝ≥0) / (((j + 1 : ℕ) : ℝ≥0))
    let k : ℕ → ℕ := fun j => (n + 1) * (j + 1)
    let mesh : ℕ → ℝ := fun j => (1 : ℝ) / ((j : ℝ) + 1)
    (let v : ℕ → ℕ → ℝ≥0 := fun n i => min (u n i) (τ ω)
     (∀ n,
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
      ENNReal.ofReal (rightLimit D 0 ω) * ENNReal.ofReal (Real.exp (-(q * 0))) +
      ((∑ i ∈ Finset.range (k n),
        ENNReal.ofReal (Real.exp (-(q * (v n (i + 1) : ℝ)))) *
          ENNReal.ofReal
            (V (x + X.X (v n (i + 1)) ω - rightLimit D (v n i) ω) -
             V (x + X.X (v n (i + 1)) ω - rightLimit D (v n (i + 1)) ω))) +
        ENNReal.ofReal (q * mesh n) *
          dividendMeasure D ω (Ioc (0 : ℝ) (τ ω : ℝ)))) ∧
     Tendsto
       (fun n =>
         (ENNReal.ofReal (q * mesh n) *
          dividendMeasure D ω (Ioc (0 : ℝ) (τ ω : ℝ))).toReal)
       atTop (𝓝 0)) := by
  intro u k mesh
  have hcell : ∀ j i, (u j (i + 1) : ℝ) - (u j i : ℝ) = mesh j := by
    intro j i
    exact (avram_jump6_B_canonical_NNReal_grid_exact_mesh_width_and_limit).1 j i
  have hmesh0 : Tendsto mesh atTop (𝓝 (0 : ℝ)) := by
    exact (avram_jump6_B_canonical_NNReal_grid_exact_mesh_width_and_limit).2
  have hm : ∀ j, 0 ≤ mesh j := by
    intro j
    dsimp [mesh]
    positivity
  have hmono : ∀ j, Monotone (u j) := by
    intro j
    apply monotone_nat_of_le_succ
    intro i
    apply NNReal.coe_le_coe.mp
    have h := hcell j i
    have hd := hm j
    linarith only [h, hd]
  have hzero : ∀ j, u j 0 = 0 := by
    intro j
    simp [u]
  have hcover : ∀ j, τ ω ≤ u j (k j) := by
    intro j
    exact avram_jump6_B_canonical_grid_reaches_bounded_clock_every_mesh n j (τ ω) hn
  have hmesh : ∀ j i, i < k j →
      (u j (i + 1) : ℝ) - (u j i : ℝ) ≤ mesh j := by
    intro j i _
    exact le_of_eq (hcell j i)
  exact avram_wave6_06_original_strict_preruin_paymentTimes_clipped_stieltjes_grid_budget
    X x C hC q hq w V hw_cont hw_smooth hw_grad hVtop hVfinite
    D hD ω τ T hτT hStrict u hmono k hzero hcover mesh hm hmesh hmesh0
