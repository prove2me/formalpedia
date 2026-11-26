-- Prove2me | solution 1 for BandParity.fixed_base_collapse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:55:26.06846+00:00
-- url     : https://prove2.me/submissions/3d47f011-03ca-45fb-b636-5cd27bfdda56

module
public import Definitions.Def_BandParity_Basic
public import Definitions.Def_BandParity_FixedBase
public import Theorems.Thm_BandParity_gi_im
public import Theorems.Thm_BandParity_gi_re
attribute [local simp] BandParity.gi_im
attribute [local simp] BandParity.gi_re



set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R]
namespace BandParity
theorem _root_.solution (χ : MulChar (ZMod p) R) {b : ZMod p} (hb : b ≠ 0) :
    (p : R) * χ b * floorSum χ b = ((b.val : R) * χ b - 1) * T χ := by
  -- the substitution `m = b n`
  have hsub : χ b * ∑ n : ZMod p, χ n * ((b * n).val : R) = T χ := by
    rw [Finset.mul_sum]
    unfold T
    refine Fintype.sum_equiv (Equiv.mulLeft₀ b hb) _ _ fun n => ?_
    simp only [Equiv.mulLeft₀_apply, map_mul]; ring
  -- `(b n).val = b.val n.val - p ⌊b.val n.val / p⌋`
  have hval : ∀ n : ZMod p, ((b * n).val : R) =
      (b.val : R) * n.val - p * ((b.val * n.val / p : ℕ) : R) := by
    intro n
    rw [ZMod.val_mul, eq_sub_iff_add_eq]
    have h := congrArg (fun x : ℕ => (x : R)) (Nat.mod_add_div (b.val * n.val) p)
    push_cast at h
    exact h
  have : ∑ n : ZMod p, χ n * ((b * n).val : R) = (b.val : R) * T χ - p * floorSum χ b := by
    unfold T floorSum
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hval]; ring
  rw [this] at hsub
  linear_combination -hsub
end BandParity
