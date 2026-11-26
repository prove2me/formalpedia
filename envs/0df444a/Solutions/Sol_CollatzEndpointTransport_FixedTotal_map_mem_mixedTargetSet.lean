-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.map_mem_mixedTargetSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:54:56.698404+00:00
-- url     : https://prove2.me/submissions/a97054ac-1f9c-4d09-832f-f3c0a1e6bc3f

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalEndpointMoment
import Mathlib.Analysis.MeanInequalities
import Definitions.Def_CollatzEndpointTransport_Linear_FiniteFiberMixture

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {ι : Type*} {α : ι → Type*} {β : Type*}
    [DecidableEq β]
    (U : Finset ι) (W : ∀ i, Finset (α i))
    (f : ∀ i, α i → β)
    {i : ι} (hi : i ∈ U) {x : α i} (hx : x ∈ W i) :
    f i x ∈ mixedTargetSet U W f := by
  exact Finset.mem_biUnion.mpr
    ⟨i, hi, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
end CollatzEndpointTransport.FixedTotal
