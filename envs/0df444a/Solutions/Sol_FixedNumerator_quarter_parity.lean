-- Prove2me | solution 1 for FixedNumerator.quarter_parity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:41:07.176627+00:00
-- url     : https://prove2.me/submissions/07f2cdcd-310e-4014-81cf-b6c39bb170c8

module
public import Definitions.Def_FixedNumerator_Defs
public import Definitions.Def_FixedNumerator_Primary
public import Theorems.Thm_FixedNumerator_norm_mod_four
public import Theorems.Thm_FixedNumerator_norm_sub_mod_eight

set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator
namespace FixedNumerator
theorem _root_.solution {a b : GaussianInt} (hb : IsPrimary b) (h : (4 : GaussianInt) ∣ a - b) :
    (a.norm - 1) / 4 % 2 = (b.norm - 1) / 4 % 2 := by
  have h8 := norm_sub_mod_eight h
  have h4 := norm_mod_four hb
  omega
end FixedNumerator
