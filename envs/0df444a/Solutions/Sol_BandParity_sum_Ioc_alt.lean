-- Prove2me | solution 1 for BandParity.sum_Ioc_alt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:02:44.401048+00:00
-- url     : https://prove2.me/submissions/bd2b07fe-a302-4af9-93a1-9c28501f620c

module
public import Definitions.Def_BandParity_Defs
public import Definitions.Def_BandParity_Matching
public import Definitions.Def_BandParity_Laws
public import Theorems.Thm_BandParity_gi_im
public import Theorems.Thm_BandParity_gi_re
attribute [local simp] BandParity.gi_im
attribute [local simp] BandParity.gi_re



set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
omit hp
namespace BandParity
theorem _root_.solution (m : ℕ) : ∑ v ∈ Ioc 0 (2 * m), (-1 : ℤ) ^ v = 0 := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring,
      Finset.sum_Ioc_succ_top (by omega), Finset.sum_Ioc_succ_top (by omega), ih,
      Odd.neg_one_pow ⟨n, rfl⟩, Even.neg_one_pow ⟨n + 1, by ring⟩]
    norm_num
end BandParity
