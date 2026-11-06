-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_ruin_clipped_caplinear_nonlinear_residual_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T14:24:41.348865+00:00
-- url     : https://prove2.me/submissions/20639a22-7f93-49b6-80d5-7ede248e348a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_global_cap_residual_grid_nonpositive
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The original BV source's downward residual remains nonpositive on
the actual ruin-clipped physical grid, including cap contact and ruin. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (q : ℝ) (T : ℝ≥0) (u : ℕ → ℝ≥0)
    (hu : Monotone u) (n : ℕ) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z else if z ≤ C.toReal then w z
      else w C.toReal + (z - C.toReal)
    ∀ᵐ ω ∂P,
      let τ : ℝ≥0 :=
        (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
      let v : ℕ → ℝ≥0 := fun i => min (u i) τ
      ∃ R : ℝ≥0 → ℝ,
        Monotone R ∧
        (∑ i : Fin n,
          Real.exp (-(q * (v i : ℝ))) *
            (V (riskProcess X x D (v i) ω -
              (R (v (i + 1)) - R (v i))) -
             V (riskProcess X x D (v i) ω))) ≤ 0 := by
  let V : ℝ → ℝ := fun z =>
    if C = ⊤ then w z else if z ≤ C.toReal then w z
    else w C.toReal + (z - C.toReal)
  have hSource :=
    avram_p3_bv_original_global_cap_residual_grid_nonpositive
      X hBV x D w C hC hw_cont hw0 hw_neg hw_smooth hw_grad q
  dsimp only at hSource ⊢
  filter_upwards [hSource] with ω hω
  let τ : ℝ≥0 :=
    (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
  let v : ℕ → ℝ≥0 := fun i => min (u i) τ
  obtain ⟨R, hRmon, hRsign⟩ := hω
  refine ⟨R, hRmon, ?_⟩
  have hvmono : Monotone v := by
    intro i j hij
    exact min_le_min (hu hij) le_rfl
  have hvstop : v n ≤ τ := by
    exact min_le_right _ _
  exact hRsign (fun _ => τ) v hvmono n hvstop
