-- Prove2me | solution 1 for BootRobust.NWDual.nw_eq_program
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:15:07.500088+00:00
-- url     : https://prove2.me/submissions/569a4dfb-36b2-46f4-9bf5-4f905a5c0285

import Mathlib
import Definitions.Def_BootRobust_NWDual_Setting

set_option autoImplicit false

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : ι → ℝ) (hD : D ∈ stdSimplex ℝ ι) (w : ι → ℝ) (hw : ∀ i, 0 < w i) (ℓ : ι → ℝ) :
    IsGreatest {x : ℝ | ∃ (s : ℝ) (P : ι → ℝ), 0 < s ∧ (∀ i, P i = D i * s) ∧
        ∑ i, P i = s ∧ ∑ i, w i * P i = 1 ∧ x = ∑ i, w i * ℓ i * P i}
      (BootRobust.Perf.nwEst w ℓ D) := by
  set Sg := ∑ i, w i * D i with hSg
  have hpos : 0 < Sg := by
    apply Finset.sum_pos'
    · intro i _; exact mul_nonneg (hw i).le (hD.1 i)
    · obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ) (f := D)
        (by rw [hD.2]; exact one_ne_zero)
      exact ⟨i, Finset.mem_univ _, mul_pos (hw i) (lt_of_le_of_ne (hD.1 i) (Ne.symm hi))⟩
  have hnw : BootRobust.Perf.nwEst w ℓ D = (∑ i, w i * ℓ i * D i) / Sg := rfl
  constructor
  · refine ⟨1 / Sg, fun i => D i * (1 / Sg), by positivity, fun i => rfl, ?_, ?_, ?_⟩
    · rw [← Finset.sum_mul, hD.2]; ring
    · have : ∑ i, w i * (D i * (1 / Sg)) = (∑ i, w i * D i) * (1 / Sg) := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring
      rw [this, ← hSg]; field_simp
    · rw [hnw]
      have : ∑ i, w i * ℓ i * (D i * (1 / Sg)) = (∑ i, w i * ℓ i * D i) * (1 / Sg) := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring
      rw [this]; ring
  · rintro x ⟨s, P, hs, hP, _, hwP, rfl⟩
    have h1 : s * Sg = 1 := by
      rw [← hwP, hSg, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [hP i]; ring
    have hs' : s = 1 / Sg := by field_simp; linarith
    rw [hnw]
    have : ∑ i, w i * ℓ i * P i = s * ∑ i, w i * ℓ i * D i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by rw [hP i]; ring
    rw [this, hs']
    apply le_of_eq
    ring
