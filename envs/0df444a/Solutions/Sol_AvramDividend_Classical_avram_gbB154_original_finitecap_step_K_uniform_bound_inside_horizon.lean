-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB154_original_finitecap_step_K_uniform_bound_inside_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T12:41:52.92621+00:00
-- url     : https://prove2.me/submissions/942a4648-447e-41b7-ab2a-08a2402da264

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB60_finitecap_clipped_gradient_uniform_bound
import Theorems.Thm_AvramDividend_Classical_avram_gbB146_uniform_real_mesh_sum_bound_on_cells
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section


theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (δ : ℝ) (hδ : 0 < δ) (j : ℕ) :
      let G : ℕ → ℕ → Ω → ℝ := fun m i ω =>
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        let a : ℝ := δ / 2
        let b : ℝ := C.toReal *
          (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
        let Y : ℝ := x + X.X s ω - rightLimit D s ω
        if s < ρ ω then Real.exp (-(q * (s : ℝ))) *
          (if Y ∈ Icc a b then deriv w Y else 1)
        else 0
    let K : ℕ → ℝ → Ω → ℝ := fun m t ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
      let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
      (Finset.range (m + 1)).sum (fun i =>
        if (s i : ℝ) ≤ t ∧ t < ((s i + Δ : ℝ≥0) : ℝ)
        then G m i ω else 0)
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (m : ℕ) (t : ℝ) (ω : Ω), t ∈ Ioo (0 : ℝ) (n : ℝ) → |K m t ω| ≤ B := by
  intro G K
  rcases avram_gbB60_finitecap_clipped_gradient_uniform_bound
      (Ω := Ω) q hq w C hC hFiniteCap hw_smooth δ hδ j
    with ⟨B, hB, hb⟩
  refine ⟨B, hB, ?_⟩
  have hG : ∀ r i η, |G r i η| ≤ B := by
    intro r i η
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((r + 1 : ℕ) : ℝ≥0)
    let s : ℝ≥0 := (i : ℝ≥0) * Δ
    have h := hb s ρ
      (fun η => x + X.X s η - rightLimit D s η) η
    simpa only [G, s, Δ] using h
  intro m t ω ht
  have hnR : (0 : ℝ) < n := lt_trans ht.1 ht.2
  have hn : 0 < n := by exact_mod_cast hnR
  have hstep := avram_gbB146_uniform_real_mesh_sum_bound_on_cells
    n hn G B hG m t ω
      (show t ∈ Ico (0 : ℝ) (n : ℝ) from ⟨le_of_lt ht.1, ht.2⟩)
  let Δnn : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
  let Δr : ℝ := (n : ℝ) / ((m : ℝ) + 1)
  have hΔ : (Δnn : ℝ) = Δr := by
    simp only [Δnn, Δr, NNReal.coe_div, NNReal.coe_natCast,
      NNReal.coe_add, NNReal.coe_one, Nat.cast_add, Nat.cast_one]
  have hlo (i : ℕ) :
      (((i : ℝ≥0) * Δnn : ℝ≥0) : ℝ) = (i : ℝ) * Δr := by
    simp only [NNReal.coe_mul, NNReal.coe_natCast, hΔ]
  have hhi (i : ℕ) :
      ((((i : ℝ≥0) * Δnn) + Δnn : ℝ≥0) : ℝ) =
        (((i + 1 : ℕ) : ℝ) * Δr) := by
    simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_natCast,
      hΔ, NNReal.coe_one, Nat.cast_add, Nat.cast_one]
    ring
  have heq : (Finset.range (m + 1)).sum (fun i =>
      if (((i : ℝ≥0) * Δnn : ℝ≥0) : ℝ) ≤ t ∧
          t < ((((i : ℝ≥0) * Δnn) + Δnn : ℝ≥0) : ℝ)
      then G m i ω else 0) =
    (Finset.range (m + 1)).sum (fun i =>
      if (i : ℝ) * Δr ≤ t ∧
          t < (((i + 1 : ℕ) : ℝ) * Δr)
      then G m i ω else 0) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hlo i, hhi i]
  change |(Finset.range (m + 1)).sum (fun i =>
    if (((i : ℝ≥0) * Δnn : ℝ≥0) : ℝ) ≤ t ∧
        t < ((((i : ℝ≥0) * Δnn) + Δnn : ℝ≥0) : ℝ)
    then G m i ω else 0)| ≤ B
  rw [heq]
  exact hstep
