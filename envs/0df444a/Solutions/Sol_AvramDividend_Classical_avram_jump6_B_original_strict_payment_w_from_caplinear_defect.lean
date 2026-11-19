-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_original_strict_payment_w_from_caplinear_defect
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T00:57:02.233522+00:00
-- url     : https://prove2.me/submissions/62793e17-4844-493c-83a4-ac5e5bd4461d

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_anycap_strict_canonical_caplinear_cash_epsilon
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_physical_payment_caplinear_overshoot_defect_exact
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_anycap_strict_each_grid_caplinear_signed_cash
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_canonical_discount_error_finite_and_vanishing
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (q : ℝ) (hq : 0 ≤ q) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (hVtop : C = ⊤ → ∀ y : ℝ, V y = w y)
    (hVfinite : C ≠ ⊤ → ∀ y : ℝ,
      V y = if y ≤ C.toReal then w y else w C.toReal + (y - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0)
    (hStrict : (t : ℝ≥0∞) < ruinTime X x D ω)
    (n : ℕ) (ht : t ≤ (n : ℝ≥0))
    (hInit : V (x - rightLimit D 0 ω) = w (x - rightLimit D 0 ω))
    (hFinal : V x = w x) :
    let v : ℕ → ℕ → ℝ≥0 := fun j i =>
      min ((i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) t
    let m : ℕ → ℕ := fun j => (n + 1) * (j + 1)
    let Cash : ℝ≥0∞ :=
      ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (t : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)
    (∀ j i : ℕ, i < m j →
      V (x + X.X (v j (i + 1)) ω - rightLimit D (v j (i + 1)) ω) =
      w (x + X.X (v j (i + 1)) ω - rightLimit D (v j (i + 1)) ω)) →
    (∀ δ : ℝ, 0 < δ → ∀ᶠ j in atTop,
      (∑ i ∈ Finset.range (m j),
        Real.exp (-(q * (v j (i + 1) : ℝ))) *
        (V (x + X.X (v j (i + 1)) ω - rightLimit D (v j i) ω) -
         w (x + X.X (v j (i + 1)) ω - rightLimit D (v j i) ω)))
       ≤ δ) →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop,
      Cash.toReal + (w (x - rightLimit D 0 ω) - w x) +
        (∑ i ∈ Finset.range (m j),
          Real.exp (-(q * (v j (i + 1) : ℝ))) *
          (w (x + X.X (v j (i + 1)) ω - rightLimit D (v j (i + 1)) ω) -
           w (x + X.X (v j (i + 1)) ω - rightLimit D (v j i) ω)))
      ≤ ε := by
  dsimp only
  intro hPost hDefect ε hε
  have hHalf : (0 : ℝ) < ε / 2 := by linarith
  have hBase :=
    avram_jump6_B_original_anycap_strict_canonical_caplinear_cash_epsilon
      X x C hC q hq w V hw_cont hw_smooth hw_grad
      hVtop hVfinite D hD ω t hStrict n ht (ε / 2) hHalf
  have hDef := hDefect (ε / 2) hHalf
  filter_upwards [hBase, hDef] with j hjBase hjDef
  let v : ℕ → ℕ → ℝ≥0 := fun a i =>
    min ((i : ℝ≥0) / ((a + 1 : ℕ) : ℝ≥0)) t
  let m : ℕ → ℕ := fun a => (n + 1) * (a + 1)
  have hId :=
    avram_jump6_B_physical_payment_caplinear_overshoot_defect_exact
      (Finset.range (m j))
      (fun i => Real.exp (-(q * (v j (i + 1) : ℝ))))
      (fun i => x + X.X (v j (i + 1)) ω - rightLimit D (v j i) ω)
      (fun i => x + X.X (v j (i + 1)) ω - rightLimit D (v j (i + 1)) ω)
      w V (x - rightLimit D 0 ω) x hInit hFinal
      (by
        intro i hi
        exact hPost j i (Finset.mem_range.mp hi))
  linarith only [hjBase, hjDef, hId]
