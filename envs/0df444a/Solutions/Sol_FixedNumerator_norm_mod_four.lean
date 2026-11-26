-- Prove2me | solution 1 for FixedNumerator.norm_mod_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:40:08.791802+00:00
-- url     : https://prove2.me/submissions/4a9ce697-9da1-482e-9960-72402e61eb00

module
public import Definitions.Def_FixedNumerator_Defs
public import Definitions.Def_FixedNumerator_Primary

set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator
namespace FixedNumerator
theorem _root_.solution {a : GaussianInt} (ha : IsPrimary a) : a.norm % 4 = 1 := by
  obtain ⟨t, ht⟩ := ha
  have ha' : a = 1 + lam3 * t := by rw [← ht]; ring
  have hn : a.norm = 1 + 4 * (-(t.re) - t.im) + 8 * (t.re ^ 2 + t.im ^ 2) := by
    rw [ha']; simp [Zsqrtd.norm, lam3]; ring
  rw [hn]; omega
end FixedNumerator
