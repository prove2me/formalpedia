-- Prove2me | solution 1 for Formalism.IncomingBounds.newton_window_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:02:58.337313+00:00
-- url     : https://prove2.me/submissions/25f5436f-4e2e-4a4f-881e-77da6ec16ee1

import Mathlib
import Definitions.Def_Formalism_IncomingBounds_LevelTail
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_AltChooseSumEqZero
import Theorems.Thm_Formalism_IncomingBounds_altChoose_sum_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset fwdDiff
open Formalism Formalism.IncomingBounds
namespace Formalism.IncomingBounds
theorem _root_.solution : NewtonWindow := by
  intro R _ I D a y0 hwin
  let f : ℕ → R := fun y => ∑ s ∈ range (D + 1), a s * ((Nat.choose y s : ℕ) : R)
  let c : ℕ → ℤ := fun k => (-1 : ℤ) ^ (D + 1 - k) * (((D + 1).choose k : ℕ) : ℤ)
  have hsm : ∀ (z : ℤ) (x : R), x ∈ I → (z : R) * x ∈ I := by
    intro z x hx
    rw [← zsmul_eq_mul]
    exact I.zsmul_mem hx z
  have hZ : ∀ y s, s ≤ D →
      ∑ k ∈ range (D + 1 + 1), (c k : R) * (((y + k).choose s : ℕ) : R) = 0 := by
    intro y s hs
    have := congrArg (Int.cast : ℤ → R) (altChoose_sum_eq_zero D s y hs)
    push_cast at this
    simpa [c] using this
  have hE : ∀ y, ∑ k ∈ range (D + 1 + 1), (c k : R) * f (y + k) = 0 := by
    intro y
    have hk : ∀ k, (c k : R) * f (y + k) =
        ∑ s ∈ range (D + 1), a s * ((c k : R) * (((y + k).choose s : ℕ) : R)) := by
      intro k
      simp only [f, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      ring
    simp_rw [hk]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro s hs
    rw [← Finset.mul_sum, hZ y s (by simp at hs; omega), mul_zero]
  have hup : ∀ t, f (y0 + t) ∈ I := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      by_cases ht : t ≤ D
      · exact hwin t ht
      · obtain ⟨u, rfl⟩ : ∃ u, t = u + (D + 1) := ⟨t - (D + 1), by omega⟩
        have h := hE (y0 + u)
        rw [Finset.sum_range_succ] at h
        have hc : (c (D + 1) : R) = 1 := by simp [c]
        rw [hc, one_mul] at h
        have hmem : ∑ k ∈ range (D + 1), (c k : R) * f (y0 + u + k) ∈ I := by
          apply AddSubgroup.sum_mem
          intro k hk
          apply hsm
          have := ih (u + k) (by simp at hk; omega)
          rwa [← add_assoc] at this
        have : f (y0 + (u + (D + 1))) = -(∑ k ∈ range (D + 1), (c k : R) * f (y0 + u + k)) := by
          rw [← add_assoc]
          linear_combination h
        rw [this]
        exact I.neg_mem hmem
  have hc0i : c 0 * c 0 = 1 := by
    simp only [c, Nat.choose_zero_right, Nat.cast_one, mul_one, Nat.sub_zero, ← mul_pow]
    simp
  have hc0 : (c 0 : R) * (c 0 : R) = 1 := by
    rw [← Int.cast_mul, hc0i, Int.cast_one]
  have hdown : ∀ m y, y0 ≤ y + m → f y ∈ I := by
    intro m
    induction m with
    | zero =>
      intro y hy
      obtain ⟨t, rfl⟩ : ∃ t, y = y0 + t := ⟨y - y0, by omega⟩
      exact hup t
    | succ m ih =>
      intro y hy
      have h := hE y
      rw [Finset.sum_range_succ'] at h
      simp only [add_zero] at h
      have hmem : ∑ k ∈ range (D + 1), (c (k + 1) : R) * f (y + (k + 1)) ∈ I := by
        apply AddSubgroup.sum_mem
        intro k _
        apply hsm
        apply ih
        omega
      have : f y = (c 0 : R) * (-(∑ k ∈ range (D + 1), (c (k + 1) : R) * f (y + (k + 1)))) := by
        linear_combination (c 0 : R) * h - (f y) * hc0
      rw [this]
      exact hsm _ _ (I.neg_mem hmem)
  intro y
  exact hdown y0 y (by omega)
end Formalism.IncomingBounds
