-- Prove2me | solution 1 for FixedNumerator.norm_sub_mod_eight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:35:44.712513+00:00
-- url     : https://prove2.me/submissions/8cbd62eb-c036-4b7e-ac00-6341cc75db9e

module
public import Definitions.Def_FixedNumerator_Defs
public import Definitions.Def_FixedNumerator_Primary

set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator
namespace FixedNumerator
theorem _root_.solution {a b : GaussianInt} (h : (4 : GaussianInt) ∣ a - b) :
    (8 : ℤ) ∣ a.norm - b.norm := by
  obtain ⟨t, ht⟩ := h
  have ha : a = b + 4 * t := by rw [← ht]; ring
  refine ⟨b.re * t.re + b.im * t.im + 2 * (t.re ^ 2 + t.im ^ 2), ?_⟩
  rw [ha]; simp [Zsqrtd.norm]; ring
end FixedNumerator
