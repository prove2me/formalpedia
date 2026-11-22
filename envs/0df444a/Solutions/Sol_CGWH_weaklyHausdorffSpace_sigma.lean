-- Prove2me | solution 1 for CGWH.weaklyHausdorffSpace_sigma
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T15:32:19.040791+00:00
-- url     : https://prove2.me/submissions/8068e79a-a483-4aa4-8036-5840fd030446

import Definitions.Def_CGWH_WeakHausdorff

open Topology TopologicalSpace

set_option autoImplicit false

universe u

open CGWH

theorem solution
    {ι : Type u} (X : ι → Type u) [∀ i, TopologicalSpace (X i)]
    [∀ i, WeaklyHausdorffSpace (X i)] : WeaklyHausdorffSpace (Σ i, X i) := by
  refine ⟨fun K _ _ _ g hg => ?_⟩
  rw [isClosed_sigma_iff]
  intro i
  let Ki : Set K := g ⁻¹' (Set.range (Sigma.mk i))
  have hKi : IsClosed Ki := isClosed_range_sigmaMk.preimage hg
  have : CompactSpace Ki := isCompact_iff_compactSpace.mp hKi.isCompact
  let gi : Ki → X i := fun k => Classical.choose k.2
  have hgi : ∀ k : Ki, Sigma.mk i (gi k) = g k := fun k => Classical.choose_spec k.2
  have hcont : Continuous gi := by
    rw [(IsOpenEmbedding.sigmaMk (i := i)).isEmbedding.continuous_iff]
    have : (Sigma.mk i ∘ gi) = fun k : Ki => g k := funext hgi
    rw [this]; exact hg.comp continuous_subtype_val
  have hcl := WeaklyHausdorffSpace.isClosed_range Ki gi hcont
  have : Sigma.mk i ⁻¹' Set.range g = Set.range gi := by
    ext x; constructor
    · rintro ⟨k, hk⟩
      refine ⟨⟨k, ⟨x, hk.symm⟩⟩, ?_⟩
      apply sigma_mk_injective (i := i)
      rw [hgi]; exact hk
    · rintro ⟨k, rfl⟩; exact ⟨k, (hgi k).symm⟩
  rw [this]; exact hcl
