-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.mixedFiberCard_eq_sigmaFiber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:36:03.20058+00:00
-- url     : https://prove2.me/submissions/be39ca85-9ed0-4b93-aaea-6939ab3e929b

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiShell
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalNonlinearShell
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real Topology
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.centralPullbackSourceCodeDecidableEq
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {ι : Type*} {α : ι → Type*} {β : Type*}
    [∀ i, DecidableEq (α i)] [DecidableEq β]
    (U : Finset ι) (W : ∀ i, Finset (α i))
    (f : ∀ i, α i → β) (b : β) :
    mixedFiberCard U W f b =
      (mapFiber (U.sigma W) (fun p => f p.1 p.2) b).card := by
  classical
  unfold mixedFiberCard mapFiber
  rw [Finset.card_filter, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.card_filter]
end CollatzEndpointTransport.FixedTotal
