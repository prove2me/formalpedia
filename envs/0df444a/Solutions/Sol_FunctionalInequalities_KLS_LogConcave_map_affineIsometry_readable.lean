-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.map_affineIsometry_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:27:18.425901+00:00
-- url     : https://prove2.me/submissions/66a3b3c4-d019-473c-953e-f3162ab309d6

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Transport

noncomputable section
open MeasureTheory Set Topology
section Transport
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
/-- Pushforward along an affine isometric embedding of a complete space preserves compact-set log-concavity
(the converse direction of `of_affineIsometry_map`; lower-dimensional images allowed, no density assumed). -/
theorem solution [CompleteSpace F]
    (ν : ProbabilityMeasure F) (hν : FunctionalInequalities.KLS.LogConcave ν)
    (μ : ProbabilityMeasure E) (f : F →ᵃⁱ[ℝ] E)
    (hmap : (μ : Measure E) = (ν : Measure F).map f) :
    FunctionalInequalities.KLS.LogConcave μ := by
  intro K L hK hL t ht0 ht1
  have hK' := f.isometry.isClosedEmbedding.isProperMap.isCompact_preimage hK
  have hL' := f.isometry.isClosedEmbedding.isProperMap.isCompact_preimage hL
  have h := hν (f ⁻¹' K) (f ⁻¹' L) hK' hL' t ht0 ht1
  have hf (x y : F) : f (t • x + (1 - t) • y) = t • f x + (1 - t) • f y := by
    simpa only [AffineMap.lineMap_apply_module, sub_sub_cancel, AffineIsometry.coe_toAffineMap]
      using f.toAffineMap.apply_lineMap x y (1 - t)
  have hc : IsCompact {z : E | ∃ x ∈ K, ∃ y ∈ L, z = t • x + (1 - t) • y} := by
    have he : {z : E | ∃ x ∈ K, ∃ y ∈ L, z = t • x + (1 - t) • y} =
        (fun p : E × E => t • p.1 + (1 - t) • p.2) '' (K ×ˢ L) := by
      ext z
      simp only [mem_ofPred_eq, mem_image, mem_prod]
      constructor
      · rintro ⟨x, hx, y, hy, rfl⟩
        exact ⟨(x, y), ⟨hx, hy⟩, rfl⟩
      · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
        exact ⟨x, hx, y, hy, rfl⟩
    rw [he]
    exact (hK.prod hL).image (by fun_prop)
  rw [hmap, Measure.map_apply f.continuous.measurable hK.measurableSet,
    Measure.map_apply f.continuous.measurable hL.measurableSet,
    Measure.map_apply f.continuous.measurable hc.measurableSet]
  apply h.trans (measure_mono ?_)
  rintro z ⟨x, hx, y, hy, rfl⟩
  exact ⟨f x, hx, f y, hy, hf x y⟩
