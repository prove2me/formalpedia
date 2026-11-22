-- Prove2me | solution 1 for CGWH.t2_imp_weaklyHausdorff_imp_t1
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T11:45:04.763823+00:00
-- url     : https://prove2.me/submissions/7685a54a-f353-4b80-87a0-46223c79fc95

import Definitions.Def_CGWH_WeakHausdorff

open Topology TopologicalSpace

set_option autoImplicit false

universe u

theorem solution (X : Type u) [TopologicalSpace X] :
    (T2Space X → CGWH.WeaklyHausdorffSpace X) ∧ (CGWH.WeaklyHausdorffSpace X → T1Space X) := by
  constructor
  · intro h
    exact ⟨fun K _ _ _ f hf => (isCompact_range hf).isClosed⟩
  · intro h
    refine ⟨fun x => ?_⟩
    have hx := h.isClosed_range PUnit.{u+1} (fun _ => x) continuous_const
    simpa [Set.range_const] using hx
