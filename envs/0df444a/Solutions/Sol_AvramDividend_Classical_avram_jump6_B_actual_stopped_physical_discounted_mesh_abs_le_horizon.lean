-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_actual_stopped_physical_discounted_mesh_abs_le_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T22:16:36.388199+00:00
-- url     : https://prove2.me/submissions/f9eb4c62-1f5c-4e45-a23e-ba8ec97bf36b

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Order.Filter.Defs
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_actual_canonical_grid_monotone_zero_and_reaches_stop_v2
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_nonuniform_clipped_discounted_generator_mesh_abs_bound
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal BigOperators
noncomputable section
set_option autoImplicit false

theorem solution
    (q : ℝ) (hq : 0 ≤ q)
    (n j : ℕ) (ρ : ℝ≥0) (hρn : ρ ≤ (n : ℝ≥0))
    (B : ℝ) (hB : 0 ≤ B) (F : ℕ → ℝ)
    (hF : ∀ i < (n + 1) * (j + 1), |F i| ≤ B) :
    let v : ℕ → ℝ≥0 := fun i =>
      min ((i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) ρ
    let m : ℕ := (n + 1) * (j + 1)
    |∑ i ∈ Finset.range m,
      Real.exp (-(q * (v (i + 1) : ℝ))) *
        (((v (i + 1) - v i : ℝ≥0) : ℝ)) * F i| ≤ (n : ℝ) * B := by
  let v : ℕ → ℝ≥0 := fun i =>
    min ((i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) ρ
  let m : ℕ := (n + 1) * (j + 1)
  obtain ⟨hv, hv0, hvm⟩ :=
    avram_jump6_B_actual_canonical_grid_monotone_zero_and_reaches_stop_v2
      n j ρ hρn
  let vr : ℕ → ℝ := fun i => (v i : ℝ)
  have hvr : Monotone vr := by
    intro a b hab
    exact_mod_cast hv hab
  have hvr0 : vr 0 = 0 := by
    change v 0 = 0 at hv0
    simp [vr, hv0]
  have hT : vr m ≤ (n : ℝ) := by
    change (v m : ℝ) ≤ (n : ℝ)
    change v m = ρ at hvm
    rw [hvm]
    exact_mod_cast hρn
  let E : ℕ → ℝ := fun i =>
    Real.exp (-(q * (v (i + 1) : ℝ)))
  have he : ∀ i < m, 0 ≤ E i ∧ E i ≤ 1 := by
    intro i hi
    constructor
    · exact le_of_lt (Real.exp_pos _)
    · have hh : 0 ≤ (v (i + 1) : ℝ) := NNReal.coe_nonneg _
      calc
        E i = Real.exp (-(q * (v (i + 1) : ℝ))) := rfl
        _ ≤ Real.exp 0 :=
          Real.exp_le_exp.mpr (neg_nonpos.mpr (mul_nonneg hq hh))
        _ = 1 := Real.exp_zero
  have hdiff (i : ℕ) :
      (((v (i + 1) - v i : ℝ≥0) : ℝ)) =
        vr (i + 1) - vr i := by
    have hh := tsub_add_cancel_of_le (hv (Nat.le_succ i))
    have hr : (((v (i + 1) - v i : ℝ≥0) : ℝ)) +
      (v i : ℝ) = (v (i + 1) : ℝ) := by exact_mod_cast hh
    dsimp [vr]
    linarith
  have heq :
      (∑ i ∈ Finset.range m,
        E i * (vr (i + 1) - vr i) * F i) =
      (∑ i ∈ Finset.range m,
        Real.exp (-(q * (v (i + 1) : ℝ))) *
          (((v (i + 1) - v i : ℝ≥0) : ℝ)) * F i) := by
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [E]
    rw [hdiff i]
  have hbound :=
    avram_jump6_B_nonuniform_clipped_discounted_generator_mesh_abs_bound
      m vr hvr hvr0 (n : ℝ) hT B hB E F he hF
  change |∑ i ∈ Finset.range m,
      Real.exp (-(q * (v (i + 1) : ℝ))) *
        (((v (i + 1) - v i : ℝ≥0) : ℝ)) * F i| ≤ (n : ℝ) * B
  rw [← heq]
  exact hbound