-- Prove2me | solution 1 for ErdosPosa.dist_lt_of_mem_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:21:59.189787+00:00
-- url     : https://prove2.me/submissions/5dd65eb4-231a-44c1-abec-5221aeddbb72

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
    (hy : y ∈ q.support) (hyx : y ≠ x) : H.dist v y < H.dist v x := by
  classical
  calc H.dist v y ≤ (q.takeUntil y hy).length := dist_le _
    _ < q.length := Walk.length_takeUntil_lt_length hy hyx
    _ = _ := hq
end ErdosPosa
