-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_arbitrary_bounded_clock_postpaid_caplinear_agrees_w
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T09:35:24.608181+00:00
-- url     : https://prove2.me/submissions/34d8ba0c-55b4-45a0-a8c7-0ccf9c86e1ee

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_clipped_grid_postpaid_caplinear_agrees_w
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hxc : ENNReal.ofReal x ≤ C)
    (w : ℝ → ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (t : ℝ≥0) (ht : t ≤ n) (ω : Ω) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z
      else if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal)
    V (x + X.X t ω - rightLimit D t ω) =
      w (x + X.X t ω - rightLimit D t ω) := by
  let V : ℝ → ℝ := fun z =>
    if C = ⊤ then w z
    else if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal)
  have hVtop : C = ⊤ → ∀ z : ℝ, V z = w z := by
    intro h z
    simp [V, h]
  have hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal) := by
    intro h z
    simp [V, h]
  have hbase :=
    avram_jump6_B_original_clipped_grid_postpaid_caplinear_agrees_w
      X x C hC hxc w V hVtop hVfinite D hD ω t n 0 n
  have hnm : n < (n + 1) * (0 + 1) := by omega
  have h : t ≤ ((n + 1 : ℕ) : ℝ≥0) := by
    exact ht.trans (by exact_mod_cast Nat.le_succ n)
  have hv : min (((n + 1 : ℕ) : ℝ≥0) /
      ((0 + 1 : ℕ) : ℝ≥0)) t = t := by
    simpa using (min_eq_right h)
  simpa only [V, Nat.zero_add, Nat.one_mul, hv] using hbase hnm
