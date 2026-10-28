-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.of_continuousLinearEquiv_map_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:27:28.428751+00:00
-- url     : https://prove2.me/submissions/7f873a13-1379-4d74-a3f3-e1c2c17684e4

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Isotropic

noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
open FunctionalInequalities.Energy FunctionalInequalities.Energy.Euclidean FunctionalInequalities.Probability
section Transport
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
/-- A probability law carried by a continuous linear equivalence inherits compact-set
log-concavity from its image law. -/
theorem solution {μ : ProbabilityMeasure E} (hμ : FunctionalInequalities.KLS.LogConcave μ)
    (ν : ProbabilityMeasure F) (T : F ≃L[ℝ] E)
    (hmap : Measure.map T (ν : Measure F) = (μ : Measure E)) : FunctionalInequalities.KLS.LogConcave ν := by
  intro K L hK hL t ht ht1
  have hm (S : Set F) (hS : IsCompact S) : (μ : Measure E) (T '' S) = (ν : Measure F) S := by
    rw [← hmap, Measure.map_apply T.continuous.measurable (hS.image T.continuous).measurableSet,
      Set.preimage_image_eq _ T.injective]
  have hcomb : T '' {z | ∃ x ∈ K, ∃ y ∈ L, z = t • x + (1 - t) • y} =
      {z | ∃ x ∈ T '' K, ∃ y ∈ T '' L, z = t • x + (1 - t) • y} := by
    have hf (x y : F) : T (t • x + (1 - t) • y) = t • T x + (1 - t) • T y := by
      rw [map_add, map_smul, map_smul]
    ext z
    constructor
    · rintro ⟨_, ⟨x, hx, y, hy, rfl⟩, rfl⟩
      exact ⟨T x, ⟨x, hx, rfl⟩, T y, ⟨y, hy, rfl⟩, hf x y⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨t • x + (1 - t) • y, ⟨x, hx, y, hy, rfl⟩, hf x y⟩
  have hc : IsCompact {z : F | ∃ x ∈ K, ∃ y ∈ L, z = t • x + (1 - t) • y} := by
    have he : {z : F | ∃ x ∈ K, ∃ y ∈ L, z = t • x + (1 - t) • y} =
        (fun p : F × F => t • p.1 + (1 - t) • p.2) '' (K ×ˢ L) := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_image, Set.mem_prod]
      constructor
      · rintro ⟨x, hx, y, hy, rfl⟩; exact ⟨(x, y), ⟨hx, hy⟩, rfl⟩
      · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩; exact ⟨x, hx, y, hy, rfl⟩
    rw [he]
    exact (hK.prod hL).image (by fun_prop)
  have h := hμ (T '' K) (T '' L) (hK.image T.continuous) (hL.image T.continuous) t ht ht1
  rwa [hm K hK, hm L hL, ← hcomb, hm _ hc] at h
