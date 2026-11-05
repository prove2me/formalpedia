-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_closed_cash_true_w_raw_jump_grid_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T23:40:17.449205+00:00
-- url     : https://prove2.me/submissions/b86663b7-fa26-4d00-8421-899ee45187b4

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_closed_grid_full_w_budget
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_stopped_discounted_raw_jump_source_grid_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/- Actual original discounted Stieltjes cash and the true w-terminal are
   controlled by physically compensated drift and raw-jump source cells. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (hx : 0 ≤ x) (C : ℝ≥0∞) (hC : 0 < C)
    (hxc : ENNReal.ofReal x ≤ C)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z else if z ≤ C.toReal then w z
      else w C.toReal + (z - C.toReal)
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    ∀ᵐ ω ∂P, ∀ (u : ℕ → ℝ≥0) (n : ℕ),
      Monotone u → u 0 = 0 →
      (∀ i : ℕ, i < n →
        u (i + 1) = 0 ∨
          (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω) →
    let Y : ℝ≥0 → ℝ := fun t =>
      x + X.X t ω - rightLimit D t ω
    let Z : ℕ → ℝ := fun i =>
      x + X.X (u (i + 1)) ω - rightLimit D (u i) ω
    E (u n) * w (Y (u n)) +
      (∫⁻ s in Icc (0 : ℝ) (u n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal ≤
      w x +
        ∑ i ∈ Finset.range n,
          ((E (u (i + 1)) - E (u i)) * V (Y (u (i + 1))) +
            E (u i) * (V (Y (u i) +
              (((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift) -
              (∑' v : ℝ≥0, if u i < v ∧ v ≤ u (i + 1) then
                Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
               else 0)) - V (Y (u i)))) := by
  intro V E
  have hRaw := avram_p3_bv_original_stopped_discounted_raw_jump_source_grid_bound
    X hBV x C hC D hD w hw_cont hw_smooth hw_grad q
  filter_upwards [hRaw] with ω hω
  intro u n hu hu0 hPre
  let Y : ℝ≥0 → ℝ := fun t =>
    x + X.X t ω - rightLimit D t ω
  let Z : ℕ → ℝ := fun i =>
    x + X.X (u (i + 1)) ω - rightLimit D (u i) ω
  have hLedger := avram_p3_bv_original_closed_grid_full_w_budget
    X x hx C hC hxc q hq w hw_cont hw_smooth hw_grad
    D hD ω u n hu hu0 hPre
  have hSource := hω u n hu hPre
  dsimp only at hLedger hSource ⊢
  calc
    _ ≤ w x +
        ∑ i ∈ Finset.range n,
          ((Real.exp (-(q * (u (i + 1) : ℝ))) -
              Real.exp (-(q * (u i : ℝ)))) *
              V (Y (u (i + 1))) +
            Real.exp (-(q * (u i : ℝ))) *
              (V (Z i) - V (Y (u i)))) := hLedger
    _ ≤ w x +
        ∑ i ∈ Finset.range n,
          ((Real.exp (-(q * (u (i + 1) : ℝ))) -
              Real.exp (-(q * (u i : ℝ)))) *
              V (Y (u (i + 1))) +
            Real.exp (-(q * (u i : ℝ))) *
              (V (Y (u i) +
                  (((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift) -
                  (∑' v : ℝ≥0, if u i < v ∧ v ≤ u (i + 1) then
                    Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
                   else 0)) - V (Y (u i)))) := by
      simp only [Finset.sum_add_distrib]
      linarith [hSource]
