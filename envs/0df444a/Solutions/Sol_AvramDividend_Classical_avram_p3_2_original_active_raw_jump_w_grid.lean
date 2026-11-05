-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_active_raw_jump_w_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T23:48:06.20321+00:00
-- url     : https://prove2.me/submissions/9691654e-69b4-42e4-9623-a3a1b1c476ee

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_negative_raw_jump_grid_caplinear_eq_w
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_postrightpayment_reserve_closed_cap

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The original admissible zero-or-strict-ruin clock automatically
keeps every left postpayment reserve below its cap, making the negative
raw-jump sum agree with the source w kernel. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (q : ℝ) (ω : Ω)
    (u : ℕ → ℝ≥0) (n : ℕ) (hu : Monotone u)
    (hActive : ∀ i : ℕ, i < n →
      u i = 0 ∨ (u i : ℝ≥0∞) < ruinTime X x D ω) :
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
  apply avram_p3_2_original_negative_raw_jump_grid_caplinear_eq_w
    X ω x D w C q u n hu
  intro i hi
  by_cases hTop : C = ⊤
  · exact Or.inl hTop
  · right
    have hClosed :=
      (avram_p4_d_dividend_postrightpayment_reserve_closed_cap
        X x C hxc D hD ω (u i) (hActive i hi)).2
    exact (ENNReal.ofReal_le_iff_le_toReal hTop).mp hClosed
