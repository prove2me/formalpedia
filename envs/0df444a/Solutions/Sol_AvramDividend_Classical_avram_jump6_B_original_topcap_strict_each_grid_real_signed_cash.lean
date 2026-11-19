-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_original_topcap_strict_each_grid_real_signed_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T22:01:32.500426+00:00
-- url     : https://prove2.me/submissions/b6a3cf81-3b04-431a-b896-6771ea5daca6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_canonical_strict_preruin_stieltjes_discount_cash
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_finite_cash_signed_source_from_true_stieltjes_envelope
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_canonical_discount_error_finite_and_vanishing
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_anycap_initial_rightpayment_postvalue_budget
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_topcap_canonical_stopped_mesh_all_payment_drops_nonnegative
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
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
    (C : ℝ≥0∞) (hC : 0 < C) (hTop : C = ⊤)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0)
    (hStrict : (t : ℝ≥0∞) < ruinTime X x D ω)
    (n : ℕ) (ht : t ≤ (n : ℝ≥0)) :
    let v : ℕ → ℕ → ℝ≥0 := fun j i =>
      min ((i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) t
    let m : ℕ → ℕ := fun j => (n + 1) * (j + 1)
    let Cash : ℝ≥0∞ :=
      ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (t : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)
    let Err : ℕ → ℝ≥0∞ := fun j =>
      ENNReal.ofReal (q * ((1 : ℝ) / ((j : ℝ) + 1))) *
        dividendMeasure D ω (Ioc (0 : ℝ) (t : ℝ))
    ∀ j, Cash.toReal + (w (x - rightLimit D 0 ω) - w x) -
      (∑ i ∈ Finset.range (m j),
        Real.exp (-(q * (v j (i + 1) : ℝ))) *
        (w (x + X.X (v j (i + 1)) ω - rightLimit D (v j i) ω) -
          w (x + X.X (v j (i + 1)) ω - rightLimit D (v j (i + 1)) ω)))
      ≤ (Err j).toReal := by
  intro v m Cash Err j
  have hTopV : C = ⊤ → ∀ y : ℝ, w y = w y := by
    intro _ y
    rfl
  have hFiniteV : C ≠ ⊤ → ∀ y : ℝ,
      w y = if y ≤ C.toReal then w y else w C.toReal + (y - C.toReal) := by
    intro h
    exact False.elim (h hTop)
  have hSt :=
    avram_jump6_B_original_canonical_strict_preruin_stieltjes_discount_cash
      X x C hC q hq w w hw_cont hw_smooth hw_grad
      hTopV hFiniteV D hD ω (fun _ => t) t (le_refl _) hStrict n ht
  dsimp only at hSt
  let E : ℕ → ℕ → ℝ := fun j i => Real.exp (-(q * (v j (i + 1) : ℝ)))
  let H : ℕ → ℕ → ℝ := fun j i =>
    w (x + X.X (v j (i + 1)) ω - rightLimit D (v j i) ω) -
      w (x + X.X (v j (i + 1)) ω - rightLimit D (v j (i + 1)) ω)
  have hCash :
      Cash ≤ ENNReal.ofReal (rightLimit D 0 ω) +
        (∑ i ∈ Finset.range (m j),
          ENNReal.ofReal (E j i) * ENNReal.ofReal (H j i)) + Err j := by
    simpa only [Cash, E, H, Err, v, m,
      mul_zero, neg_zero, Real.exp_zero, ENNReal.ofReal_one,
      mul_one, add_assoc] using hSt.1 j
  have hErr : Err j ≠ ⊤ :=
    (avram_jump6_B_original_canonical_discount_error_finite_and_vanishing
      D hD.1.1 ω t q hq).1 j
  have hD0 : 0 ≤ rightLimit D 0 ω := by
    have h := dividendStrategy_le_rightLimit D hD.1.1 ω 0
    simpa only [hD.1.1.1 ω] using h
  have hInit := avram_jump6_B_original_anycap_initial_rightpayment_postvalue_budget
    X x C hC hxc D hD w hw_cont hw_smooth hw_grad q ω
  have hReal :=
    avram_jump6_B_original_finite_cash_signed_source_from_true_stieltjes_envelope
      (Finset.range (m j)) (rightLimit D 0 ω) (w x)
      (w (x - rightLimit D 0 ω)) (E j) (H j) Cash (Err j)
      hD0 (by intro i hi; exact le_of_lt (Real.exp_pos _))
      (by
        intro i hi
        simpa only [H, v] using
          (avram_jump6_B_original_topcap_canonical_stopped_mesh_all_payment_drops_nonnegative
            X x C hC hTop w hw_cont hw_smooth hw_grad
            D hD ω t hStrict j i))
      hInit hErr hCash
  exact hReal
