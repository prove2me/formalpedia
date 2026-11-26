-- Prove2me | solution 1 for BandParity.cosetSum_add_cosetSum_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:55:35.057624+00:00
-- url     : https://prove2.me/submissions/d087b370-76bc-4573-972e-eb8dbd4a74b6

module
public import Definitions.Def_BandParity_Pin
public import Definitions.Def_BandParity_FixedBase
public import Definitions.Def_BandParity_CosetSums
public import Theorems.Thm_BandParity_cosetSum_eq_sum_ite
public import Theorems.Thm_BandParity_gi_im
public import Theorems.Thm_BandParity_gi_re
public import Theorems.Thm_BandParity_val_neg_of_ne_zero
attribute [local simp] BandParity.gi_im
attribute [local simp] BandParity.gi_re



set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ
omit hχ
namespace BandParity
theorem _root_.solution (hodd : χ (-1) = -1) (z : GaussianInt) (hz0 : z ≠ 0) :
    cosetSum χ z + cosetSum χ (-z) =
      p * (univ.filter (fun n : ZMod p => χ n = z)).card := by
  have hneg : cosetSum χ (-z) = ∑ n : ZMod p, if χ n = z then ((p : ℤ) - n.val) else 0 := by
    rw [cosetSum_eq_sum_ite]
    refine (Fintype.sum_equiv (Equiv.neg (ZMod p)) _ _ fun n => ?_).symm
    simp only [Equiv.neg_apply]
    have hχn : χ (-n) = -χ n := by rw [show -n = -1 * n by ring, map_mul, hodd, neg_one_mul]
    simp only [hχn, neg_inj]
    by_cases h : χ n = z
    · have hn0 : n ≠ 0 := by rintro rfl; exact hz0 (h.symm.trans (MulChar.map_zero χ))
      have := ZMod.val_lt n
      simp only [h, ↓reduceIte, val_neg_of_ne_zero hn0]
      push_cast [Nat.cast_sub this.le]; ring
    · simp [h]
  rw [hneg, cosetSum_eq_sum_ite, ← Finset.sum_add_distrib]
  rw [show (p : ℤ) * (univ.filter (fun n : ZMod p => χ n = z)).card =
      ∑ n : ZMod p, if χ n = z then (p : ℤ) else 0 by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]]
  refine Finset.sum_congr rfl fun n _ => ?_
  split_ifs <;> ring
end BandParity
