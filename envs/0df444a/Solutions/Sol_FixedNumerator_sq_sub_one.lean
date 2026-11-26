-- Prove2me | solution 1 for FixedNumerator.sq_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:35:34.000408+00:00
-- url     : https://prove2.me/submissions/48ff6d1f-7824-4409-bf3d-fb6169d39d6c

module
public import Definitions.Def_FixedNumerator_Defs
public import Definitions.Def_FixedNumerator_Primary

set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator
namespace FixedNumerator
theorem _root_.solution {π : GaussianInt} (hπ : IsPrimary π) : (4 : GaussianInt) ∣ π ^ 2 - 1 := by
  obtain ⟨t, ht⟩ := hπ
  have hπ' : π = 1 + lam3 * t := by rw [← ht]; ring
  refine ⟨⟨-1, 1⟩ * t + ⟨0, -2⟩ * t ^ 2, ?_⟩
  rw [hπ']
  simp only [lam3]
  ext <;> simp [pow_two] <;> ring
end FixedNumerator
