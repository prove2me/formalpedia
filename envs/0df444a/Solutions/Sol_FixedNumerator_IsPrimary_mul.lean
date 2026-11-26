-- Prove2me | solution 1 for FixedNumerator.IsPrimary.mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:35:22.785306+00:00
-- url     : https://prove2.me/submissions/8dc491a9-8a34-4bfc-9fac-8ba4e013e030

module
public import Definitions.Def_FixedNumerator_Defs
public import Definitions.Def_FixedNumerator_Primary

set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator
namespace FixedNumerator
namespace IsPrimary
theorem _root_.solution {a b : GaussianInt} (ha : IsPrimary a) (hb : IsPrimary b) :
    IsPrimary (a * b) := by
  obtain ⟨s, hs⟩ := ha
  obtain ⟨t, ht⟩ := hb
  refine ⟨s * (b - 1) + s + t, ?_⟩
  have : a * b - 1 = (a - 1) * (b - 1) + (a - 1) + (b - 1) := by ring
  rw [this, hs, ht]; ring
end IsPrimary
end FixedNumerator
