-- Prove2me | solution 1 for FewExperts.eq_1_softmin_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:43:32.763939+00:00
-- url     : https://prove2.me/submissions/c16a4236-0ad1-4a25-9793-4bb2d94572e4

import Mathlib
import Definitions.Def_FewExperts_softmin

open FewExperts in
theorem solution (N : ℕ) [NeZero N] (η : ℝ) (hη : 0 < η) (a : Fin N → ℝ) :
    (⨅ i, a i) - Real.log N / η ≤ softmin η a ∧ softmin η a ≤ ⨅ i, a i := by
  obtain ⟨i0, hi0⟩ := exists_eq_ciInf_of_finite (f := a)
  have hle : ∀ i, (⨅ j, a j) ≤ a i := fun i => ciInf_le (Set.finite_range a).bddBelow i
  have hNpos : (0:ℝ) < (N:ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  have hS1 : Real.exp (-η * (⨅ j, a j)) ≤ ∑ i, Real.exp (-η * a i) := by
    rw [← hi0]
    exact Finset.single_le_sum (f := fun i => Real.exp (-η * a i))
      (fun i _ => (Real.exp_pos _).le) (Finset.mem_univ i0)
  have hS2 : ∑ i, Real.exp (-η * a i) ≤ (N:ℝ) * Real.exp (-η * (⨅ j, a j)) := by
    calc ∑ i, Real.exp (-η * a i) ≤ ∑ _i : Fin N, Real.exp (-η * (⨅ j, a j)) :=
          Finset.sum_le_sum (fun i _ => Real.exp_le_exp.mpr (by nlinarith [hle i]))
      _ = (N:ℝ) * Real.exp (-η * (⨅ j, a j)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hL1 : -η * (⨅ j, a j) ≤ Real.log (∑ i, Real.exp (-η * a i)) := by
    have := Real.log_le_log (Real.exp_pos _) hS1
    rwa [Real.log_exp] at this
  have hL2 : Real.log (∑ i, Real.exp (-η * a i)) ≤ Real.log N + -η * (⨅ j, a j) := by
    have := Real.log_le_log (lt_of_lt_of_le (Real.exp_pos _) hS1) hS2
    rwa [Real.log_mul hNpos.ne' (Real.exp_pos _).ne', Real.log_exp] at this
  have hinv : 0 < 1 / η := one_div_pos.mpr hη
  unfold softmin
  constructor
  · have h := mul_le_mul_of_nonneg_left hL2 hinv.le
    have e : 1 / η * (Real.log N + -η * (⨅ j, a j)) = Real.log N / η - (⨅ j, a j) := by
      field_simp <;> ring
    rw [e] at h
    linarith
  · have h := mul_le_mul_of_nonneg_left hL1 hinv.le
    have e : 1 / η * (-η * (⨅ j, a j)) = -(⨅ j, a j) := by
      field_simp
    rw [e] at h
    linarith
