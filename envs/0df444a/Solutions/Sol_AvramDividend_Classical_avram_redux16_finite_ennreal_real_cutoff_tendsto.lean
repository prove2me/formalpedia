-- Prove2me | solution 1 for AvramDividend.Classical.avram_redux16_finite_ennreal_real_cutoff_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T11:45:51.954193+00:00
-- url     : https://prove2.me/submissions/1d9cf1ab-52d4-4f51-9ed5-19fbe5d882e9

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Order.MonotoneConvergence
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_finite_reciprocal_cutoff_tsum_toReal_iSup
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology MeasureTheory AvramDividend.Classical
open scoped ENNReal
noncomputable section
/-- Reciprocal positive real thresholds exhaust every finite ENNReal series. -/
theorem solution
    {α : Type*} (f : α → ℝ≥0∞) (hfinite : (∑' a : α, f a) < ⊤) :
    Tendsto (fun k : ℕ =>
      (∑' a : α,
        if ENNReal.ofReal (1 / ((k : ℝ) + 1)) < f a then f a else 0).toReal)
      atTop (𝓝 ((∑' a : α, f a).toReal)) := by
  let g : ℕ → ℝ := fun j =>
    (∑' a : α, if (j : ℝ≥0∞)⁻¹ < f a then f a else 0).toReal
  have hbelow (j : ℕ) :
      (∑' a : α, if (j : ℝ≥0∞)⁻¹ < f a then f a else 0) ≠ ⊤ := by
    apply ne_of_lt
    apply lt_of_le_of_lt _ hfinite
    apply ENNReal.tsum_le_tsum
    intro a
    split_ifs <;> simp
  have hmono : Monotone g := by
    intro i j hij
    have hijE : (i : ℝ≥0∞) ≤ (j : ℝ≥0∞) := by exact_mod_cast hij
    have hinv : (j : ℝ≥0∞)⁻¹ ≤ (i : ℝ≥0∞)⁻¹ :=
      ENNReal.inv_le_inv.mpr hijE
    apply ENNReal.toReal_mono (hbelow j)
    apply ENNReal.tsum_le_tsum
    intro a
    by_cases hi : (i : ℝ≥0∞)⁻¹ < f a
    · have hj : (j : ℝ≥0∞)⁻¹ < f a := lt_of_le_of_lt hinv hi
      simp [hi, hj]
    · simp [hi]
  have hSup : (⨆ j : ℕ, g j) = (∑' a : α, f a).toReal :=
    avram_p3_a_bvdrift_finite_reciprocal_cutoff_tsum_toReal_iSup f hfinite
  have hlim : Tendsto g atTop (𝓝 ((∑' a : α, f a).toReal)) := by
    have hbounded : BddAbove (Set.range g) := by
      refine ⟨(∑' a : α, f a).toReal, ?_⟩
      rintro y ⟨j, rfl⟩
      apply ENNReal.toReal_mono (ne_of_lt hfinite)
      apply ENNReal.tsum_le_tsum
      intro a
      split_ifs <;> simp
    simpa only [hSup] using (tendsto_atTop_ciSup hmono hbounded)
  have hshift := hlim.comp (tendsto_add_atTop_nat 1)
  have hthreshold (k : ℕ) :
      ENNReal.ofReal (1 / ((k : ℝ) + 1)) = ((k + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
    have hp : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    rw [one_div, ENNReal.ofReal_inv_of_pos hp]
    congr 1
    have hcast : (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) := by norm_cast
    rw [hcast, ENNReal.ofReal_natCast]
  simpa only [g, Function.comp_def, ← hthreshold] using hshift
