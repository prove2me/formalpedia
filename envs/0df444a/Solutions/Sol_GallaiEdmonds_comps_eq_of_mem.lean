-- Prove2me | solution 1 for GallaiEdmonds.comps_eq_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:01:44.034728+00:00
-- url     : https://prove2.me/submissions/78c2f176-8a5c-4e80-8b82-7bab0eb9b776

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEComponents
public import Theorems.Thm_GallaiEdmonds_comps_eq_cc

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmonds
variable {V : Type*}
variable {G : SimpleGraph V} {W W' S : Set V} {x y z : V}
namespace GallaiEdmonds
theorem _root_.solution {K K' : Set V} (hK : K ∈ comps G W) (hK' : K' ∈ comps G W)
    (hy : y ∈ K) (hy' : y ∈ K') : K = K' := by
  rw [comps_eq_cc hK hy, comps_eq_cc hK' hy']
end GallaiEdmonds
