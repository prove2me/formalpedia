-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_08_original_preruin_full_grid_right_endpoint_mesh_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T07:49:24.089509+00:00
-- url     : https://prove2.me/submissions/efd12743-82ac-4b81-81d2-95e3eebf4b0c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_positive_cap_original_right_endpoint_stieltjes_error
import Theorems.Thm_AvramDividend_Classical_lintegral_Ioc_partition_fin

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Real source pre-ruin full-Stieltjes grid, with total error q times mesh width times mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (q : ℝ) (hq : 0 ≤ q) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ, V z = if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (u : ℕ → ℝ≥0) (hu : Monotone u)
    (n : ℕ) (m : ℝ) (hm : 0 ≤ m)
    (hmesh : ∀ i < n, ((u (i + 1) : ℝ) - (u i : ℝ)) ≤ m)
    (hPre : ∀ i < n, u (i + 1) = 0 ∨ (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω) :
    (∫⁻ s in Ioc (u 0 : ℝ) (u n : ℝ), ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
      (∑ i ∈ Finset.range n, ENNReal.ofReal (Real.exp (-(q * (u (i + 1) : ℝ)))) *
        ENNReal.ofReal (V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
          V (x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω))) +
      ENNReal.ofReal (q * m) * dividendMeasure D ω (Ioc (u 0 : ℝ) (u n : ℝ)) := by
  let μ : Measure ℝ := dividendMeasure D ω
  let E : ℕ → ℝ≥0∞ := fun i => ENNReal.ofReal (Real.exp (-(q * (u (i + 1) : ℝ))))
  let A : ℕ → ℝ≥0∞ := fun i => ENNReal.ofReal (V (x + X.X (u (i + 1)) ω -
    rightLimit D (u i) ω) - V (x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω))
  let J : ℕ → ℝ≥0∞ := fun i =>
    ∫⁻ s in Ioc (u i : ℝ) (u (i + 1) : ℝ), ENNReal.ofReal (Real.exp (-(q * s))) ∂μ
  let B : ℕ → ℝ≥0∞ := fun i => μ (Ioc (u i : ℝ) (u (i + 1) : ℝ))
  have huR : Monotone (fun i : ℕ => (u i : ℝ)) := fun i j hij => by exact_mod_cast hu hij
  have hMass : (∑ i ∈ Finset.range n, B i) = μ (Ioc (u 0 : ℝ) (u n : ℝ)) := by
    have h := lintegral_Ioc_partition_fin μ (fun _ => (1 : ℝ≥0∞)) (fun i : ℕ => (u i : ℝ)) huR n
    simpa [B, MeasureTheory.lintegral_const] using h.symm
  have hGrid : (∫⁻ s in Ioc (u 0 : ℝ) (u n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂μ) = ∑ i ∈ Finset.range n, J i := by
    simpa [J] using lintegral_Ioc_partition_fin μ
      (fun s : ℝ => ENNReal.ofReal (Real.exp (-(q * s)))) (fun i : ℕ => (u i : ℝ)) huR n
  have hCell (i : ℕ) (hi : i ∈ Finset.range n) :
      J i ≤ E i * A i + ENNReal.ofReal (q * m) * B i := by
    have hStep : u i ≤ u (i + 1) := hu (Nat.le_succ i)
    have hmStep : q * ((u (i + 1) : ℝ) - (u i : ℝ)) ≤ q * m :=
      mul_le_mul_of_nonneg_left (hmesh i (Finset.mem_range.mp hi)) hq
    have hh : J i ≤ E i * A i + ENNReal.ofReal (q * ((u (i + 1) : ℝ) - (u i : ℝ))) * B i := by
      simpa [μ, J, E, A, B] using
        avram_wave6_08_positive_cap_original_right_endpoint_stieltjes_error X x C hC q hq w V
          hw_cont hw_smooth hw_grad hVtop hVfinite D hD ω (u i) (u (i + 1)) hStep (hPre i (Finset.mem_range.mp hi))
    calc
      J i ≤ E i * A i +
        ENNReal.ofReal (q * ((u (i + 1) : ℝ) - (u i : ℝ))) * B i := hh
      _ ≤ E i * A i + ENNReal.ofReal (q * m) * B i := by
        exact add_le_add le_rfl
          (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hmStep) bot_le)
  change (∫⁻ s in Ioc (u 0 : ℝ) (u n : ℝ), ENNReal.ofReal (Real.exp (-(q * s))) ∂μ) ≤
    (∑ i ∈ Finset.range n, E i * A i) + ENNReal.ofReal (q * m) * μ (Ioc (u 0 : ℝ) (u n : ℝ))
  calc
    (∫⁻ s in Ioc (u 0 : ℝ) (u n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂μ) =
      ∑ i ∈ Finset.range n, J i := hGrid
    _ ≤ ∑ i ∈ Finset.range n,
      (E i * A i + ENNReal.ofReal (q * m) * B i) :=
      Finset.sum_le_sum hCell
    _ = (∑ i ∈ Finset.range n, E i * A i) +
        ENNReal.ofReal (q * m) * μ (Ioc (u 0 : ℝ) (u n : ℝ)) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hMass]
