-- Prove2me | solution 1 for Experiments.norm_replace_steps_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:52:50.568298+00:00
-- url     : https://prove2.me/submissions/e22b7200-8838-4638-836b-d963729fc9b5

import Mathlib
import Definitions.Def_Experiments_NonstandardSemigroup

set_option autoImplicit true
open Filter NormedSpace Set
open scoped Topology
noncomputable section
open Experiments
variable {A : Type*} [NormedRing A]
namespace Experiments
theorem _root_.solution (M E : ℝ → A) (h0 : M 0 = 1)
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → M (s + t) = M s * M t)
    (hEadd : ∀ s t, 0 ≤ s → 0 ≤ t → E (s + t) = E s * E t) {t C D : ℝ}
    (hC : ∀ s ∈ Icc 0 t, ‖M s‖ ≤ C) (hD : ∀ s ∈ Icc 0 t, ‖E s‖ ≤ D) {h k : ℝ} (hh : 0 ≤ h)
    (hk : 0 ≤ k) (n : ℕ) {r : ℝ} (hr : 0 ≤ r) (hnh : n * h ≤ t) (hnk : n * k + r ≤ t) :
    ‖M (n * h) * E r - E (n * k + r)‖ ≤ n * (C * D * ‖M h - E k‖) := by
  induction n generalizing r with
  | zero => simp [h0]
  | succ n ih =>
    have hu : 0 ≤ (n : ℝ) * h := mul_nonneg n.cast_nonneg hh
    have hv : 0 ≤ (n : ℝ) * k := mul_nonneg n.cast_nonneg hk
    rw [Nat.cast_add_one, add_one_mul] at hnh hnk
    have hut : (n : ℝ) * h ∈ Icc 0 t := ⟨hu, by linarith⟩
    have hrt : r ∈ Icc 0 t := ⟨hr, by linarith⟩
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC _ hut)
    have heq : M ((n + 1 : ℕ) * h) * E r - E ((n + 1 : ℕ) * k + r) =
        M (n * h) * (M h - E k) * E r + (M (n * h) * E (k + r) - E (n * k + (k + r))) := by
      rw [Nat.cast_add_one, add_one_mul, add_one_mul, hadd _ _ hu hh, hEadd _ _ hk hr, add_assoc]
      noncomm_ring
    rw [heq]
    calc
      _ ≤ ‖M (n * h) * (M h - E k) * E r‖ + ‖M (n * h) * E (k + r) - E (n * k + (k + r))‖ :=
        norm_add_le _ _
      _ ≤ C * ‖M h - E k‖ * D + n * (C * D * ‖M h - E k‖) :=
        add_le_add
          (norm_mul₃_le.trans (mul_le_mul (mul_le_mul_of_nonneg_right (hC _ hut) (norm_nonneg _))
            (hD _ hrt) (norm_nonneg _) (mul_nonneg hC0 (norm_nonneg _))))
          (ih (add_nonneg hk hr) (by linarith) (by linarith))
      _ = ((n + 1 : ℕ) : ℝ) * (C * D * ‖M h - E k‖) := by
        push_cast
        ring
end Experiments
