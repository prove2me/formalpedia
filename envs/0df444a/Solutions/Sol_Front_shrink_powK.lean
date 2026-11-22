-- Prove2me | solution 1 for Front.shrink_powK
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:43:51.782442+00:00
-- url     : https://prove2.me/submissions/667b69ed-8847-4212-98cd-1557eec55db4

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
theorem _root_.solution {e : ℕ → ℕ} (k : ℕ) :
    shrink (powK M k) (M ∘ e) = powK (M ∘ e) k := by
  ext s
  simp only [shrink, powK, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨hlen, hp, _⟩, hMe⟩; exact ⟨hlen, hp, hMe⟩
  · rintro ⟨hlen, hp, hMe⟩
    refine ⟨⟨hlen, hp, fun x hx => ?_⟩, hMe⟩
    obtain ⟨i, rfl⟩ := hMe x hx
    exact ⟨e i, rfl⟩
end Front
