-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_c_bvchain_original_initial_discounted_product_source_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:29:09.721903+00:00
-- url     : https://prove2.me/submissions/be6bcb66-693a-4300-8e04-d9d5c7fe5198

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_discounted_full_grid_product_budget
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_public_original_anycap_book_postpayment_V_eq_w
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_original_zero_atom_postpayment_ledger_entry

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hxc : ENNReal.ofReal x ≤ C)
    (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (u : ℕ → ℝ≥0) (n : ℕ) (hzero : u 0 = 0)
    (hGrid : ∀ i : ℕ, i < n → u i ≤ u (i + 1))
    (hPre : ∀ i : ℕ, i < n →
      (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω) :
    let e : ℕ → ℝ := fun i => Real.exp (-(q * (u i : ℝ)))
    let cash : ℕ → ℝ := fun i =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Ioc (u i : ℝ) (u (i + 1) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal
    let post : ℕ → ℝ := fun i =>
      V (x + X.X (u i) ω - rightLimit D (u i) ω)
    let source : ℕ → ℝ := fun i =>
      V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
      V (x + X.X (u i) ω - rightLimit D (u i) ω)
    rightLimit D 0 ω + (∑ i ∈ Finset.range n, cash i) +
      e n * w (x + X.X (u n) ω - rightLimit D (u n) ω) ≤
      w x + (∑ i ∈ Finset.range n, e i * source i) +
      ∑ i ∈ Finset.range n, (e (i + 1) - e i) * post (i + 1) := by
  classical
  let e : ℕ → ℝ := fun i => Real.exp (-(q * (u i : ℝ)))
  let cash : ℕ → ℝ := fun i =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Ioc (u i : ℝ) (u (i + 1) : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal
  let post : ℕ → ℝ := fun i =>
    V (x + X.X (u i) ω - rightLimit D (u i) ω)
  let source : ℕ → ℝ := fun i =>
    V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
      V (x + X.X (u i) ω - rightLimit D (u i) ω)
  change rightLimit D 0 ω + (∑ i ∈ Finset.range n, cash i) +
      e n * w (x + X.X (u n) ω - rightLimit D (u n) ω) ≤
      w x + (∑ i ∈ Finset.range n, e i * source i) +
        ∑ i ∈ Finset.range n, (e (i + 1) - e i) * post (i + 1)
  have hBudget :
      (∑ i ∈ Finset.range n, cash i) +
        e n * post n - e 0 * post 0 ≤
      (∑ i ∈ Finset.range n, e i * source i) +
        ∑ i ∈ Finset.range n, (e (i + 1) - e i) * post (i + 1) := by
    exact avram_p3_c_bvchain_original_discounted_full_grid_product_budget
      X x C hC w V hw_cont hw_smooth hw_grad hVtop hVfinite
      D hD ω q hq u n hGrid hPre
  have hEq0 := (avram_p3_c_bvchain_public_original_anycap_book_postpayment_V_eq_w
    X x C hC hxc w V hVtop hVfinite D hD ω 0).2
  have hEqn := (avram_p3_c_bvchain_public_original_anycap_book_postpayment_V_eq_w
    X x C hC hxc w V hVtop hVfinite D hD ω (u n)).2
  have hPost0 : post 0 = w (x - rightLimit D 0 ω) := by
    dsimp [post]
    rw [hzero]
    simpa only [X.X_zero, add_zero] using hEq0
  have hPostN :
      post n = w (x + X.X (u n) ω - rightLimit D (u n) ω) := by
    exact hEqn
  have hE0 : e 0 = 1 := by
    simp [e, hzero]
  have hInitial :=
    avram_wave7_08_source_original_zero_atom_postpayment_ledger_entry
      X w x C D hD hjump ω
  rw [hE0, one_mul, hPost0, hPostN] at hBudget
  linarith only [hBudget, hInitial]
