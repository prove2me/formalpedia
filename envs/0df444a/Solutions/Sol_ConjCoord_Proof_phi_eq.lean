-- Prove2me | solution 1 for ConjCoord.Proof.phi_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:51:32.967077+00:00
-- url     : https://prove2.me/submissions/18be4912-d456-4fed-98b4-2ba9e43227ef

module
public import Definitions.Def_ConjCoord_Compute
public import Definitions.Def_ConjCoord_TwoSquares
public import Definitions.Def_ConjCoord_Main
public import Theorems.Thm_ConjCoord_Proof_sum_Icc_natAbs


set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof
namespace ConjCoord.Proof
theorem _root_.solution (n : ℕ) :
    phi n = 4 * (tCoeff n + ∑ k ∈ range n,
      2 * (if (k + 1) ^ 2 ≤ n then tCoeff (n - (k + 1) ^ 2) else 0)) := by
  unfold phi
  set F : ℕ → ℤ := fun k => if k ^ 2 ≤ n then tCoeff (n - k ^ 2) else 0 with hF
  have hw : ∀ w : ℤ, (if w ^ 2 ≤ (n : ℤ) then tCoeff (n - (w ^ 2).toNat) else 0) = F w.natAbs := by
    intro w
    have hc : w ^ 2 = ((w.natAbs ^ 2 : ℕ) : ℤ) := by push_cast; exact (sq_abs w).symm
    simp only [hF, hc, Int.toNat_natCast, Nat.cast_le]
  simp_rw [hw]
  rw [sum_Icc_natAbs n F, sum_range_succ']
  simp only [wt, Nat.add_one_ne_zero, ite_false, ite_true, one_smul, hF, zero_pow two_ne_zero,
    zero_le, Nat.sub_zero, nsmul_eq_mul, Nat.cast_ofNat]
  ring
end ConjCoord.Proof
