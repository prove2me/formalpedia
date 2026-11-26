-- Prove2me | solution 1 for FixedNumerator.two_le_norm_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:37:12.816365+00:00
-- url     : https://prove2.me/submissions/63b7dfd7-a1a1-4627-9e1f-1468f002d406

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
theorem _root_.solution {π : GaussianInt} (hπ : Prime π) : 2 ≤ π.norm := by
  have h0 : π.norm ≠ 0 := by
    intro h
    exact hπ.ne_zero ((Zsqrtd.norm_eq_zero_iff (by norm_num) π).mp h)
  have h1 : π.norm ≠ 1 := fun h => hπ.not_isUnit ((Zsqrtd.norm_eq_one_iff' (by norm_num) π).mp h)
  have := norm_nonneg' π
  omega
end FixedNumerator
