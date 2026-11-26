-- Prove2me | solution 1 for FixedNumerator.ne_zero_of_four_dvd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:43:41.268774+00:00
-- url     : https://prove2.me/submissions/2464b67b-01ac-4464-8b1a-68db6f911a28

module
public import Definitions.Def_FixedNumerator_Local
public import Definitions.Def_FixedNumerator_Split
public import Theorems.Thm_FixedNumerator_not_four_dvd_zero_sub

set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator
namespace FixedNumerator
theorem _root_.solution {b c : GaussianInt} (hb : IsPrimary b) (h : (4 : GaussianInt) ∣ c - b) :
    c ≠ 0 := by
  rintro rfl; exact not_four_dvd_zero_sub hb h
end FixedNumerator
