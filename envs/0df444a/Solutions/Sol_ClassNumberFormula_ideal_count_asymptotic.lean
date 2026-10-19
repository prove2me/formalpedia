-- Prove2me | solution 1 for ClassNumberFormula.ideal_count_asymptotic
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T13:32:32.965386+00:00
-- url     : https://prove2.me/submissions/48d7df31-9e36-4e45-b966-0852f535f014

import Mathlib

open NumberField NumberField.InfinitePlace NumberField.Units Filter Topology Real

namespace CNIC

theorem main (K : Type*) [Field K] [NumberField K] :
    Tendsto (fun N : ℕ =>
        (Nat.card {I : Ideal (𝓞 K) // 1 ≤ Ideal.absNorm I ∧ Ideal.absNorm I ≤ N} : ℝ) / N)
      atTop (𝓝 ((2 : ℝ) ^ nrRealPlaces K * (2 * π) ^ nrComplexPlaces K * regulator K *
          classNumber K / (torsionOrder K * Real.sqrt |(discr K : ℝ)|))) := by
  have h := (NumberField.Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop
  refine h.congr fun N => ?_
  simp only [Function.comp_apply, Nat.cast_le]
  congr 2
  apply Nat.card_congr
  exact {
    toFun := fun I => ⟨I.1.1, by
      have h1 : I.1.1 ≠ ⊥ := fun h => by
        have := I.1.2
        rw [h] at this
        exact zero_notMem_nonZeroDivisors this
      refine ⟨?_, I.2⟩
      rw [Nat.one_le_iff_ne_zero]
      intro h0
      exact h1 (Ideal.absNorm_eq_zero_iff.mp h0)⟩
    invFun := fun I => ⟨⟨I.1, by
      apply mem_nonZeroDivisors_of_ne_zero
      intro h0
      have := I.2.1
      rw [show (I.1 : Ideal (𝓞 K)) = ⊥ from h0, Ideal.absNorm_bot] at this
      exact absurd this (by norm_num)⟩, I.2.2⟩
    left_inv := fun I => rfl
    right_inv := fun I => rfl }

end CNIC

theorem solution (K : Type*) [Field K] [NumberField K] :
    Tendsto (fun N : ℕ =>
        (Nat.card {I : Ideal (𝓞 K) // 1 ≤ Ideal.absNorm I ∧ Ideal.absNorm I ≤ N} : ℝ) / N)
      atTop (𝓝 ((2 : ℝ) ^ nrRealPlaces K * (2 * π) ^ nrComplexPlaces K * regulator K *
          classNumber K / (torsionOrder K * Real.sqrt |(discr K : ℝ)|))) :=
  CNIC.main K
