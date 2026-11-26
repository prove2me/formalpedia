-- Prove2me | solution 1 for FixedNumerator.IsPrimary.of_dvd_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:37:31.967813+00:00
-- url     : https://prove2.me/submissions/214a39fe-a175-4f94-b721-fe172ef0cbb4

module
public import Definitions.Def_FixedNumerator_Defs
public import Definitions.Def_FixedNumerator_Primary
public import Theorems.Thm_FixedNumerator_lam3_dvd_four

set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator
namespace FixedNumerator
namespace IsPrimary
theorem _root_.solution {a b : GaussianInt} (hb : IsPrimary b) (h : (4 : GaussianInt) ∣ a - b) :
    IsPrimary a := by
  have h' : lam3 ∣ a - b := dvd_trans lam3_dvd_four h
  have : a - 1 = (a - b) + (b - 1) := by ring
  rw [IsPrimary, this]; exact dvd_add h' hb
end IsPrimary
end FixedNumerator
