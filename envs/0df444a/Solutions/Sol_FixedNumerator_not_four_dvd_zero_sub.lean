-- Prove2me | solution 1 for FixedNumerator.not_four_dvd_zero_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:42:21.047665+00:00
-- url     : https://prove2.me/submissions/a683871a-fb3d-41e9-b33e-f7f412112441

module
public import Definitions.Def_FixedNumerator_Local
public import Definitions.Def_FixedNumerator_Split
public import Theorems.Thm_FixedNumerator_norm_lam3
public import Theorems.Thm_FixedNumerator_lam3_dvd_four


set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator
namespace FixedNumerator
theorem _root_.solution {b : GaussianInt} (hb : IsPrimary b) :
    ¬ (4 : GaussianInt) ∣ 0 - b := by
  intro h
  have h1 : lam3 ∣ (0 - b) + (b - 1) := dvd_add (dvd_trans lam3_dvd_four h) hb
  have h2 : lam3 ∣ 1 := by
    have : (0 - b) + (b - 1) = -1 := by ring
    rw [this] at h1; exact (dvd_neg).mp h1
  have hu : IsUnit lam3 := isUnit_of_dvd_one h2
  have := (Zsqrtd.norm_eq_one_iff' (by norm_num) lam3).mpr hu
  rw [norm_lam3] at this; norm_num at this
end FixedNumerator
