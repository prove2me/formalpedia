-- Prove2me | solution 1 for BandParity.isPrimitiveRoot_gi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:55:09.199287+00:00
-- url     : https://prove2.me/submissions/dacb1e24-db74-4ea6-a397-67743c644c13

module
public import Definitions.Def_BandParity_Basic
public import Definitions.Def_BandParity_Pin
public import Theorems.Thm_BandParity_gi_im
public import Theorems.Thm_BandParity_gi_ne_one
public import Theorems.Thm_BandParity_gi_pow_four
public import Theorems.Thm_BandParity_gi_re
public import Theorems.Thm_BandParity_gi_sq
public import Theorems.Thm_BandParity_neg_one_ne_one
attribute [local simp] BandParity.gi_im
attribute [local simp] BandParity.gi_re



set_option autoImplicit true
@[expose] public section
public section
open BandParity
variable {p : ℕ} [hp : Fact p.Prime]
namespace BandParity
theorem _root_.solution : IsPrimitiveRoot gi 4 := by
  refine IsPrimitiveRoot.mk_of_lt gi (by norm_num) gi_pow_four fun l hl0 hl4 h => ?_
  interval_cases l
  · exact absurd (pow_one gi ▸ h) gi_ne_one
  · rw [gi_sq] at h; exact absurd h neg_one_ne_one
  · rw [pow_succ, gi_sq] at h
    have := congrArg Zsqrtd.re h; simp at this
end BandParity
