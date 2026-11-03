-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_06_actual_clipped_preruin_full_stieltjes_grid_budget_and_vanishing_mass_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T09:37:14.127257+00:00
-- url     : https://prove2.me/submissions/01b0dd4d-db78-4cc8-b8bc-d54c5dd98eec

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_preruin_full_grid_right_endpoint_mesh_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_moving_grid_full_dividend_mass_mesh_error_vanish
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_clipped_source_cell_mesh_nonexpansive
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
/-- The same original D and ruin-localised clipped grid retain the *entire*
    Stieltjes mass; its only right-endpoint discount error vanishes. -/
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
    (hPre : τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω)
    (u : ℕ → ℕ → ℝ≥0) (hu : ∀ n, Monotone (u n))
    (k : ℕ → ℕ) (hzero : ∀ n, u n 0 = 0)
    (hcover : ∀ n, τ ω ≤ u n (k n))
    (mesh : ℕ → ℝ) (hm : ∀ n, 0 ≤ mesh n)
    (hmesh : ∀ n i, i < k n →
      ((u n (i + 1) : ℝ) - (u n i : ℝ)) ≤ mesh n)
    (hmesh0 : Tendsto mesh atTop (𝓝 0)) :
    (let v : ℕ → ℕ → ℝ≥0 := fun n i => min (u n i) (τ ω)
     (∀ n,
      (∫⁻ s in Ioc (0 : ℝ) (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
      (∑ i ∈ Finset.range (k n),
        ENNReal.ofReal (Real.exp (-(q * (v n (i + 1) : ℝ)))) *
          ENNReal.ofReal
            (V (x + X.X (v n (i + 1)) ω - rightLimit D (v n i) ω) -
             V (x + X.X (v n (i + 1)) ω - rightLimit D (v n (i + 1)) ω))) +
        ENNReal.ofReal (q * mesh n) *
          dividendMeasure D ω (Ioc (0 : ℝ) (τ ω : ℝ))) ∧
     Tendsto
       (fun n =>
         (ENNReal.ofReal (q * mesh n) *
          dividendMeasure D ω (Ioc (0 : ℝ) (τ ω : ℝ))).toReal)
       atTop (𝓝 0)) := by
  let v : ℕ → ℕ → ℝ≥0 := fun n i => min (u n i) (τ ω)
  have hvMono (n : ℕ) : Monotone (v n) := by
    intro i j hij
    exact min_le_min (hu n hij) le_rfl
  have hvMesh (n i : ℕ) (hi : i < k n) :
      ((v n (i + 1) : ℝ) - (v n i : ℝ)) ≤ mesh n := by
    exact avram_wave6_06_original_clipped_source_cell_mesh_nonexpansive
      (u n) (hu n) i (τ ω) (mesh n) (hm n) (hmesh n i hi)
  have hvPre (n i : ℕ) (hi : i < k n) :
      v n (i + 1) = 0 ∨ (v n (i + 1) : ℝ≥0∞) < ruinTime X x D ω := by
    rcases hPre with hzeroτ | hstrict
    · left
      simp [v, hzeroτ]
    · right
      have hle : (v n (i + 1) : ℝ≥0∞) ≤ (τ ω : ℝ≥0∞) := by
        exact_mod_cast (min_le_right (u n (i + 1)) (τ ω))
      exact lt_of_le_of_lt hle hstrict
  have hvStart (n : ℕ) : v n 0 = 0 := by simp [v, hzero n]
  have hvEnd (n : ℕ) : v n (k n) = τ ω := min_eq_right (hcover n)
  constructor
  · intro n
    have h := avram_wave6_08_original_preruin_full_grid_right_endpoint_mesh_budget
      X x C hC q hq w V hw_cont hw_smooth hw_grad hVtop hVfinite
      D hD ω (v n) (hvMono n) (k n) (mesh n) (hm n) (hvMesh n) (hvPre n)
    simpa only [hvStart n, hvEnd n, NNReal.coe_zero] using h
  · have h := avram_wave6_08_original_moving_grid_full_dividend_mass_mesh_error_vanish
      D hD.1.1 ω q hq T v hvMono k (fun n => by rw [hvEnd]; exact hτT) mesh hm hmesh0
    simpa only [hvStart, hvEnd, NNReal.coe_zero] using h
