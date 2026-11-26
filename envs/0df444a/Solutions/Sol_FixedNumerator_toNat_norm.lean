-- Prove2me | solution 1 for FixedNumerator.toNat_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:38:59.55719+00:00
-- url     : https://prove2.me/submissions/6202b11a-aaec-49cc-8ede-fd45dffc0b93

module
public import Definitions.Def_FixedNumerator_Local
public import Definitions.Def_FixedNumerator_Split
public import Theorems.Thm_P2M_FixedNumerator_norm_nonneg__64b3937061ea

set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator
namespace FixedNumerator
theorem _root_.solution (c : GaussianInt) : (c.norm.toNat : ℤ) = c.norm :=
  Int.toNat_of_nonneg (norm_nonneg' c)
end FixedNumerator
