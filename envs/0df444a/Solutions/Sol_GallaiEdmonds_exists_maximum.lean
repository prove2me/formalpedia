-- Prove2me | solution 1 for GallaiEdmonds.exists_maximum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:07:56.235303+00:00
-- url     : https://prove2.me/submissions/b58fe1af-1ffc-441b-8470-d8bd503ce021

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEConstruct
public import Definitions.Def_GallaiEdmondsLib_GallaiEdmonds
public import Theorems.Thm_GallaiEdmonds_tb_eq


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmonds
variable {V : Type*} (G : SimpleGraph V)
namespace GallaiEdmonds
theorem _root_.solution [Finite V] : ∃ M : G.Subgraph, IsMaximumMatching G M := by
  obtain ⟨M, -, hM, hmax, -⟩ := tb_eq G
  exact ⟨M, hM, hmax⟩
end GallaiEdmonds
