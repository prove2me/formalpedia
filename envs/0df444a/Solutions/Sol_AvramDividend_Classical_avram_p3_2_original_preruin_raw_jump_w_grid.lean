-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_preruin_raw_jump_w_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T00:01:57.909316+00:00
-- url     : https://prove2.me/submissions/229ec0ee-79ce-4290-ab52-6c649b13243a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_active_raw_jump_w_grid

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Physical pre-ruin right endpoints force every left endpoint to be
an admissible active time, including the time-zero cell. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (q : ℝ) (ω : Ω)
    (u : ℕ → ℝ≥0) (n : ℕ)
    (hu : Monotone u) (hu0 : u 0 = 0)
    (hPre : ∀ i : ℕ, i < n →
      u (i + 1) = 0 ∨ (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z else if z ≤ C.toReal then w z
      else w C.toReal + (z - C.toReal)
    (∑ i ∈ Finset.range n,
      Real.exp (-(q * (u i : ℝ))) *
        (V ((x + X.X (u i) ω - rightLimit D (u i) ω) -
          (∑' v : ℝ≥0, if u i < v ∧ v ≤ u (i + 1) then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
          else 0)) -
        V (x + X.X (u i) ω - rightLimit D (u i) ω))) =
    (∑ i ∈ Finset.range n,
      Real.exp (-(q * (u i : ℝ))) *
        (w ((x + X.X (u i) ω - rightLimit D (u i) ω) -
          (∑' v : ℝ≥0, if u i < v ∧ v ≤ u (i + 1) then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
          else 0)) -
        w (x + X.X (u i) ω - rightLimit D (u i) ω))) := by
  intro V
  apply avram_p3_2_original_active_raw_jump_w_grid
    X x C hxc D hD w q ω u n hu
  intro i hi
  cases i with
  | zero =>
      exact Or.inl hu0
  | succ j =>
      have hj : j < n := by omega
      simpa only [Nat.succ_eq_add_one] using hPre j hj
