-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_b21_original_uniform_floor_samples_converge_from_left
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T18:43:02.387877+00:00
-- url     : https://prove2.me/submissions/2a3e2d8e-d703-4267-b992-19ac533b20ca

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Filter
open scoped Topology
noncomputable section

/-- Original uniform-grid floor samples approach each time from the left. -/
theorem solution (T t : ℝ) (hT : 0 < T) (ht : 0 ≤ t) :
    (∀ n : ℕ,
      T * (⌊(t / T) * ((n : ℝ) + 2)⌋₊ : ℝ) / ((n : ℝ) + 2) ≤ t) ∧
    Tendsto
      (fun n : ℕ => T * (⌊(t / T) * ((n : ℝ) + 2)⌋₊ : ℝ) /
        ((n : ℝ) + 2))
      atTop (𝓝 t) := by
  have hratio : 0 ≤ t / T := div_nonneg ht hT.le
  have hfloor (n : ℕ) :
      (⌊(t / T) * ((n : ℝ) + 2)⌋₊ : ℝ) ≤
        (t / T) * ((n : ℝ) + 2) :=
    Nat.floor_le (mul_nonneg hratio (by positivity))
  have hleft (n : ℕ) :
      T * (⌊(t / T) * ((n : ℝ) + 2)⌋₊ : ℝ) /
        ((n : ℝ) + 2) ≤ t := by
    apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 2)).2
    calc
      T * (⌊(t / T) * ((n : ℝ) + 2)⌋₊ : ℝ) ≤
          T * ((t / T) * ((n : ℝ) + 2)) :=
        mul_le_mul_of_nonneg_left (hfloor n) hT.le
      _ = t * ((n : ℝ) + 2) := by
        field_simp [ne_of_gt hT]
  have hlimit :=
    (tendsto_nat_floor_mul_div_atTop hratio).comp
      tendsto_natCast_atTop_atTop
  have hshift := (tendsto_add_atTop_iff_nat 2).2 hlimit
  have hshift' :
      Tendsto
        (fun n : ℕ => (⌊(t / T) * ((n : ℝ) + 2)⌋₊ : ℝ) /
          ((n : ℝ) + 2))
        atTop (𝓝 (t / T)) := by
    simpa only [Function.comp_apply, Nat.cast_add, Nat.cast_ofNat] using hshift
  refine ⟨hleft, ?_⟩
  convert (tendsto_const_nhds (x := T)).mul hshift' using 1
  · ext n
    ring
  · field_simp [ne_of_gt hT]
