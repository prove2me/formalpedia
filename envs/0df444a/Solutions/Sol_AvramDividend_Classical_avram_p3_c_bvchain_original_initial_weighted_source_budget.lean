-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_c_bvchain_original_initial_weighted_source_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:29:04.01644+00:00
-- url     : https://prove2.me/submissions/a29b532b-2ed0-48f6-a7d4-30ec2419c621

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_weighted_source_product_budget
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
      (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω)
    (r : ℕ → ℝ) (hr : ∀ i : ℕ, i < n → 0 ≤ r (i + 1))
    (hr0 : r 0 = 1) :
    let cash : ℕ → ℝ := fun i =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Ioc (u i : ℝ) (u (i + 1) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal
    let post : ℕ → ℝ := fun i =>
      w (x + X.X (u i) ω - rightLimit D (u i) ω)
    let source : ℕ → ℝ := fun i =>
      V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
      V (x + X.X (u i) ω - rightLimit D (u i) ω)
    rightLimit D 0 ω +
      (∑ i ∈ Finset.range n, r (i + 1) * cash i) +
        r n * post n ≤
      w x + (∑ i ∈ Finset.range n, r (i + 1) * source i) +
        ∑ i ∈ Finset.range n, (r (i + 1) - r i) * post i := by
  classical
  let cash : ℕ → ℝ := fun i =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Ioc (u i : ℝ) (u (i + 1) : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal
  let post : ℕ → ℝ := fun i =>
    w (x + X.X (u i) ω - rightLimit D (u i) ω)
  let source : ℕ → ℝ := fun i =>
    V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
      V (x + X.X (u i) ω - rightLimit D (u i) ω)
  change rightLimit D 0 ω +
      (∑ i ∈ Finset.range n, r (i + 1) * cash i) +
        r n * post n ≤
      w x + (∑ i ∈ Finset.range n, r (i + 1) * source i) +
        ∑ i ∈ Finset.range n, (r (i + 1) - r i) * post i
  have hWeighted :
      (∑ i ∈ Finset.range n, r (i + 1) * cash i) +
        r n * post n - r 0 * post 0 ≤
      (∑ i ∈ Finset.range n, r (i + 1) * source i) +
        ∑ i ∈ Finset.range n, (r (i + 1) - r i) * post i := by
    exact avram_p3_c_bvchain_original_weighted_source_product_budget
      X x C hC hxc w V hw_cont hw_smooth hw_grad hVtop hVfinite
      D hD ω q hq u n hGrid hPre r hr
  have hZero : post 0 = w (x - rightLimit D 0 ω) := by
    simp only [post, hzero, X.X_zero, add_zero]
  have hInitial :=
    avram_wave7_08_source_original_zero_atom_postpayment_ledger_entry
      X w x C D hD hjump ω
  rw [hr0, hZero] at hWeighted
  linarith only [hWeighted, hInitial]
