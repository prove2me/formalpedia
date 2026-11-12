-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger113_original_interior_contact_mesh_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T14:13:14.209486+00:00
-- url     : https://prove2.me/submissions/b848e1c2-e1a0-4339-9067-7e1fbe970aa1

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger99_original_interior_contact_cells_sum_bound
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Strict interior original dividend-contact corrections consume one mesh width. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (ρ : ℝ≥0) (u : ℝ) (hu : 0 ≤ u)
    (hprefix : ∀ t : ℝ≥0, 0 < t → t < ρ →
      u ≤ riskProcess X x D t ω)
    (v : ℕ → ℝ≥0) (hv : Monotone v) (k : ℕ)
    (hinterior : ∀ i : ℕ, i < k → v (i + 1) < ρ)
    (hfinite : ∀ i : ℕ, i < k →
      dividendMeasure D ω (Ioc (v i : ℝ) (v (i + 1) : ℝ)) ≠ ⊤)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hTopCap : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (δ M : ℝ) (hδ : 0 ≤ δ)
    (hmesh : ∀ i : ℕ, i < k → (v (i + 1) : ℝ) - (v i : ℝ) ≤ δ)
    (hMass : (Finset.sum (Finset.range k) (fun i =>
      (dividendMeasure D ω (Ioc (v i : ℝ) (v (i + 1) : ℝ))).toReal)) ≤ M) :
    (Finset.sum (Finset.range k) (fun i =>
      (∫⁻ s in Ioc (v i : ℝ) (v (i + 1) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal +
      Real.exp (-(q * (v (i + 1) : ℝ))) *
        (w (x + X.X (v (i + 1)) ω - rightLimit D (v (i + 1)) ω) -
          w (x + X.X (v (i + 1)) ω - rightLimit D (v i) ω)))) ≤
      q * δ * M := by
  have hcell := avram_gledger99_original_interior_contact_cells_sum_bound
    X x D hD ω ρ u hu hprefix v hv k hinterior hfinite q hq w C
    hTopCap hw0 hw_cont hw_neg hw_grad
  have hmeshbudget :
      (∑ i ∈ Finset.range k,
        q * ((v (i + 1) : ℝ) - (v i : ℝ)) *
          (dividendMeasure D ω (Ioc (v i : ℝ) (v (i + 1) : ℝ))).toReal) ≤
      q * δ * (∑ i ∈ Finset.range k,
        (dividendMeasure D ω (Ioc (v i : ℝ) (v (i + 1) : ℝ))).toReal) := by
    calc
      _ ≤ ∑ i ∈ Finset.range k,
          q * δ * (dividendMeasure D ω
            (Ioc (v i : ℝ) (v (i + 1) : ℝ))).toReal := by
        apply Finset.sum_le_sum
        intro i hi
        have hm : 0 ≤ q * (dividendMeasure D ω
            (Ioc (v i : ℝ) (v (i + 1) : ℝ))).toReal :=
          mul_nonneg hq ENNReal.toReal_nonneg
        calc
          _ = (q * (dividendMeasure D ω
            (Ioc (v i : ℝ) (v (i + 1) : ℝ))).toReal) *
              ((v (i + 1) : ℝ) - (v i : ℝ)) := by ring
          _ ≤ (q * (dividendMeasure D ω
            (Ioc (v i : ℝ) (v (i + 1) : ℝ))).toReal) * δ :=
              mul_le_mul_of_nonneg_left (hmesh i (Finset.mem_range.mp hi)) hm
          _ = _ := by ring
      _ = _ := by rw [Finset.mul_sum]
  exact hcell.trans (hmeshbudget.trans
    (mul_le_mul_of_nonneg_left hMass (mul_nonneg hq hδ)))
