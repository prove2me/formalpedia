-- Prove2me | solution 1 for CGWH.weaklyHausdorffSpace_subtype_and_compactlyGenerated
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T15:29:27.15887+00:00
-- url     : https://prove2.me/submissions/615e5b74-d916-4f2c-8234-3f12ab8280d3

import Definitions.Def_CGWH_WeakHausdorff

open Topology TopologicalSpace

set_option autoImplicit false

universe u

open CGWH

theorem solution
    (X : Type u) [TopologicalSpace X] [WeaklyHausdorffSpace X] :
    (∀ s : Set X, WeaklyHausdorffSpace s) ∧
      @WeaklyHausdorffSpace X (TopologicalSpace.compactlyGenerated.{u} X) := by
  constructor
  · intro s
    refine ⟨fun K _ _ _ f hf => ?_⟩
    have h := WeaklyHausdorffSpace.isClosed_range K (fun k => (f k : X))
      (continuous_subtype_val.comp hf)
    have : Set.range f = Subtype.val ⁻¹' (Set.range fun k => (f k : X)) := by
      ext y; constructor
      · rintro ⟨k, rfl⟩; exact ⟨k, rfl⟩
      · rintro ⟨k, hk⟩; exact ⟨k, Subtype.ext hk⟩
    rw [this]; exact h.preimage continuous_subtype_val
  · have hle : TopologicalSpace.compactlyGenerated.{u} X ≤ (inferInstance : TopologicalSpace X) := by
      simp only [compactlyGenerated, ← continuous_iff_coinduced_le, continuous_sigma_iff,
        Sigma.forall]
      exact fun S f ↦ f.2
    refine @WeaklyHausdorffSpace.mk X (TopologicalSpace.compactlyGenerated.{u} X)
      (fun K _ _ _ f hf => ?_)
    have hf' : Continuous f := by
      rw [continuous_def] at hf ⊢
      intro s hs
      exact hf s (hle s hs)
    have h := WeaklyHausdorffSpace.isClosed_range K f hf'
    exact @IsClosed.mk X (TopologicalSpace.compactlyGenerated.{u} X) _ (hle _ h.isOpen_compl)
