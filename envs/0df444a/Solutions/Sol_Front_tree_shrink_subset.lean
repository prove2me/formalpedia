-- Prove2me | solution 1 for Front.tree_shrink_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:43:52.185158+00:00
-- url     : https://prove2.me/submissions/293e196a-9b4a-46aa-bd5e-bcc0f448ef97

module
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Rank
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Shrink

set_option autoImplicit true
@[expose] public section
public section
open Set List
noncomputable section
open Front
variable {F : Set (List ℕ)} {M : ℕ → ℕ}
namespace Front
theorem _root_.solution {N : ℕ → ℕ} : tree (shrink F N) ⊆ tree F := by
  rintro s ⟨u, hu, hpre⟩
  exact ⟨u, hu.1, hpre⟩
end Front
