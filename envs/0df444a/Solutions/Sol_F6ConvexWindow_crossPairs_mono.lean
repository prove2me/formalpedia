-- Prove2me | solution 1 for F6ConvexWindow.crossPairs_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:47:53.230579+00:00
-- url     : https://prove2.me/submissions/610cfd0a-26d0-4c44-aca5-d683d6f5dc93

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15

set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]
namespace F6ConvexWindow
theorem _root_.solution {U U' W W' : Finset V} (hU : U ⊆ U') (hW : W ⊆ W') :
    crossPairs U W ⊆ crossPairs U' W' := by
  classical
  intro P hP
  obtain ⟨x, hx, hPx⟩ := mem_biUnion.mp hP
  obtain ⟨y, hy, rfl⟩ := mem_image.mp hPx
  exact mem_biUnion.mpr ⟨x, hU hx, mem_image.mpr
    ⟨y, mem_filter.mpr ⟨hW (mem_filter.mp hy).1, (mem_filter.mp hy).2⟩, rfl⟩⟩
end F6ConvexWindow
