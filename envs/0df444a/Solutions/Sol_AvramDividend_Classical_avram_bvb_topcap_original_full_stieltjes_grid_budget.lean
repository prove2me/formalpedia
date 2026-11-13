-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_topcap_original_full_stieltjes_grid_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T12:27:36.722633+00:00
-- url     : https://prove2.me/submissions/3c77dbe7-75f3-44ae-9943-b9a7ebbc2764

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_cap_original_global_real_signed_stieltjes_grid_nonpos

import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_actual_original_controlled_leftclock_full_stieltjes_terminal_reward_grid_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (q : ℝ) (hq : 0 ≤ q) (hCapTop : C = ⊤) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (u : ℕ → ℝ≥0) (n : ℕ)
    (hu : Monotone u) (hu0 : u 0 = 0)
    (hPre : ∀ i : ℕ, i < n →
      u (i + 1) = 0 ∨
        (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω) :
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t =>
      x + X.X t ω - rightLimit D t ω
    let Z : ℕ → ℝ := fun i =>
      x + X.X (u (i + 1)) ω - rightLimit D (u i) ω
    E (u n) * w (Y (u n)) +
      (∫⁻ s in Icc (0 : ℝ) (u n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal ≤
      w x +
        ∑ i ∈ Finset.range n,
          ((E (u (i + 1)) - E (u i)) * w (Y (u (i + 1))) +
            E (u i) * (w (Z i) - w (Y (u i)))) := by
  have hVtop : C = ⊤ → ∀ z : ℝ, w z = w z := by
    intro _ z
    rfl
  have hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      w z = if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal) := by
    intro hNot
    exact False.elim (hNot hCapTop)
  exact
    avram_wave5_03_actual_original_controlled_leftclock_full_stieltjes_terminal_reward_grid_bound
      X x C hC q hq w w hw_cont hw_smooth hw_grad
      hVtop hVfinite D hD ω u n hu hu0 hPre
