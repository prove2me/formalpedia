-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB213_generic_stopped_clipped_NNReal_uniform_grid_amplitude
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:12:16.169052+00:00
-- url     : https://prove2.me/submissions/429fb237-7c22-4b1e-81f0-b921f331253b

import Mathlib
import Mathlib.Analysis.Calculus.Deriv.Basic
import Theorems.Thm_AvramDividend_Classical_avram_gbB212_stopped_discounted_compact_clip_uniform_amplitude
import Theorems.Thm_AvramDividend_Classical_avram_gbB146_uniform_real_mesh_sum_bound_on_cells
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- One mesh coefficient remains uniformly bounded after real-time cell selection. -/
theorem solution
    {Ω : Type*} (Y : ℝ≥0 → Ω → ℝ)
    (ρ : Ω → ℝ≥0) (w : ℝ → ℝ)
    (a b : ℝ) (hContinuous : ContinuousOn (deriv w) (Icc a b))
    (q : ℝ) (hq : 0 ≤ q) (n : ℕ) (hn : 0 < n) :
    let G : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      if s < ρ ω then Real.exp (-(q * (s : ℝ))) *
        (if Y s ω ∈ Icc a b then deriv w (Y s ω) else 1)
      else 0
    let K : ℕ → ℝ → Ω → ℝ := fun m t ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
      (Finset.range (m + 1)).sum (fun i =>
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        if (s : ℝ) ≤ t ∧ t < ((s + Δ : ℝ≥0) : ℝ)
        then G m i ω else 0)
    ∃ B : ℝ, 0 ≤ B ∧ ∀ m t ω,
      t ∈ Ioo (0 : ℝ) (n : ℝ) → |K m t ω| ≤ B := by
  intro G K
  obtain ⟨B, hB, hb⟩ :=
    avram_gbB212_stopped_discounted_compact_clip_uniform_amplitude
      w a b hContinuous q hq Y ρ
  refine ⟨B, hB, ?_⟩
  have hG : ∀ m i ω, |G m i ω| ≤ B := by
    intro m i ω
    simpa only [G] using
      (hb ((i : ℝ≥0) * ((n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0))) ω)
  intro m t ω ht
  have hnR : (0 : ℝ) < n := lt_trans ht.1 ht.2
  have hn' : 0 < n := by exact_mod_cast hnR
  have hstep := avram_gbB146_uniform_real_mesh_sum_bound_on_cells
    n hn' G B hG m t ω
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

