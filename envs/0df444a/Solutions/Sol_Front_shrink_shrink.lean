-- Prove2me | solution 1 for Front.shrink_shrink
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:43:43.87888+00:00
-- url     : https://prove2.me/submissions/2880fb46-8c7b-4aad-a281-9f3ac51bdf2a

module
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Rank
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Shrink
public import Theorems.Thm_Front_isInit_nil
attribute [local simp] Front.isInit_nil



set_option autoImplicit true
@[expose] public section
public section
open Set List
noncomputable section
open Front
variable {F : Set (List ℕ)} {M : ℕ → ℕ}
namespace Front
theorem _root_.solution {N N' : ℕ → ℕ} (h : Set.range N' ⊆ Set.range N) :
    shrink (shrink F N) N' = shrink F N' := by
  ext s
  simp only [shrink, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨hsF, _⟩, hN'⟩; exact ⟨hsF, hN'⟩
  · rintro ⟨hsF, hN'⟩; exact ⟨⟨hsF, fun x hx => h (hN' x hx)⟩, hN'⟩
end Front
