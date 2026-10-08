-- Prove2me | solution 1 for DouglasRachfordPPA.GenDR.zero_iff_resolvent_fixed
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T07:17:07.176881+00:00
-- url     : https://prove2.me/submissions/a63f50b1-842f-490b-9f55-368c9075e356

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_DouglasRachfordPPA_GenDR_Operators

open InnerProductSpace ThreeOpSplitting.Convergence

open InnerProductSpace ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR in
theorem a54e445b_mem_resolvent {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : H → Set H) (c : ℝ) (x z : H) :
    z ∈ opResolvent c T x ↔ ∃ u ∈ T z, x = z + c • u := by
  simp only [opResolvent, opInv, opAdd, opId, opSmul, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨y, rfl, w, ⟨u, hu, rfl⟩, h⟩
    exact ⟨u, hu, h⟩
  · rintro ⟨u, hu, h⟩
    exact ⟨z, rfl, c • u, ⟨u, hu, rfl⟩, h⟩

open InnerProductSpace ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR in
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H → Set H) (hT : IsMaximalMonotone T) (c : ℝ) (hc : 0 < c) (x : H) :
    (0 : H) ∈ T x ↔ opResolvent c T x = {x} := by
  constructor
  · intro h0
    ext z
    rw [a54e445b_mem_resolvent, Set.mem_singleton_iff]
    constructor
    · rintro ⟨u, hu, hx⟩
      have hm := hT.1 z x u 0 hu h0
      have hcu : c • u = x - z := by rw [hx]; abel
      have hu' : u = c⁻¹ • (x - z) := by
        rw [← hcu, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
      rw [hu', sub_zero, inner_smul_right] at hm
      have hneg : ⟪z - x, x - z⟫_ℝ = -‖z - x‖ ^ 2 := by
        rw [← neg_sub z x, inner_neg_right, real_inner_self_eq_norm_sq]
      rw [hneg] at hm
      have hci : 0 < c⁻¹ := inv_pos.mpr hc
      have : ‖z - x‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖z - x‖]
      have : ‖z - x‖ = 0 := by nlinarith [norm_nonneg (z - x)]
      exact sub_eq_zero.mp (norm_eq_zero.mp this)
    · rintro rfl
      exact ⟨0, h0, by simp⟩
  · intro h
    have hx : x ∈ opResolvent c T x := by rw [h]; rfl
    obtain ⟨u, hu, hxu⟩ := (a54e445b_mem_resolvent T c x x).mp hx
    have hcu : c • u = 0 := by
      have := congrArg (· - x) hxu
      simpa using this.symm
    rcases smul_eq_zero.mp hcu with hc0 | hu0
    · exact absurd hc0 hc.ne'
    · exact hu0 ▸ hu
