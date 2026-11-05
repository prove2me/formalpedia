-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_closed_grid_full_w_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T21:08:53.822846+00:00
-- url     : https://prove2.me/submissions/437be8e6-0762-436a-b085-4929faab579c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_explicit_caplinear_source_mesh
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_public_original_anycap_book_postpayment_V_eq_w
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_caplinear_extension_eq_w_closed_cap

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/- Complete original finite-grid verification ledger, with the genuine
initial w x and genuine postpayment w terminal; only cells use V. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (hx : 0 ≤ x) (C : ℝ≥0∞) (hC : 0 < C)
    (hxc : ENNReal.ofReal x ≤ C)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (u : ℕ → ℝ≥0) (n : ℕ)
    (hu : Monotone u) (hu0 : u 0 = 0)
    (hPre : ∀ i : ℕ, i < n →
      u (i + 1) = 0 ∨
        (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z else if z ≤ C.toReal then w z
      else w C.toReal + (z - C.toReal)
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
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
            E (u i) * (V (Z i) - V (Y (u i)))) := by
  let V : ℝ → ℝ := fun z =>
    if C = ⊤ then w z else if z ≤ C.toReal then w z
    else w C.toReal + (z - C.toReal)
  have hVtop : C = ⊤ → ∀ z : ℝ, V z = w z := by
    intro h z
    simp [V, h]
  have hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal) := by
    intro h z
    simp [V, h]
  have hInitial := avram_wave5_04b_positive_caplinear_extension_eq_w_closed_cap
    C hC w V hVtop hVfinite x hx hxc
  have hTerminal :=
    (avram_p3_c_bvchain_public_original_anycap_book_postpayment_V_eq_w
      X x C hC hxc w V hVtop hVfinite D hD ω (u n)).2
  have hGrid := avram_p3_bv_original_explicit_caplinear_source_mesh
    X x C hC q hq w hw_cont hw_smooth hw_grad D hD ω u n hu hu0 hPre
  let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
  let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
  let Z : ℕ → ℝ := fun i =>
    x + X.X (u (i + 1)) ω - rightLimit D (u i) ω
  have hGrid' : E (u n) * V (Y (u n)) +
      (∫⁻ s in Icc (0 : ℝ) (u n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal ≤
      V x + ∑ i ∈ Finset.range n,
        ((E (u (i + 1)) - E (u i)) * V (Y (u (i + 1))) +
          E (u i) * (V (Z i) - V (Y (u i)))) := hGrid
  rw [hInitial, hTerminal] at hGrid'
  exact hGrid'
