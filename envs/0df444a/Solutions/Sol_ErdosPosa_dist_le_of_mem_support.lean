-- Prove2me | solution 1 for ErdosPosa.dist_le_of_mem_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:22:00.942823+00:00
-- url     : https://prove2.me/submissions/0a65bd42-4efe-42d1-bb51-0b748210f399

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPCyc
public import Definitions.Def_ErdosPosaLib_EPMoore

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*} {H : SimpleGraph V}
namespace ErdosPosa
theorem _root_.solution {v x y : V} (q : H.Walk v x) (hq : q.length = H.dist v x)
    (hy : y ∈ q.support) : H.dist v y ≤ H.dist v x := by
  classical
  calc H.dist v y ≤ (q.takeUntil y hy).length := dist_le _
    _ ≤ q.length := Walk.length_takeUntil_le_length _ _
    _ = _ := hq
end ErdosPosa
