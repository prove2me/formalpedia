-- Prove2me | solution 1 for CGSpace.sequentialSpace_iff_exists_isQuotientMap_metrizable
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T11:58:40.507172+00:00
-- url     : https://prove2.me/submissions/3e9101cf-3c71-4718-81be-5a9ab053d6fc

import Mathlib

open Topology TopologicalSpace

set_option autoImplicit false

universe u

namespace Sol_CGSpace_sequentialSpace_iff_exists_isQuotientMap_metrizable

open Filter

/-- A disjoint union of locally compact spaces is locally compact. -/
theorem locallyCompactSpace_sigma {ι : Type*} {E : ι → Type*} [∀ i, TopologicalSpace (E i)]
    [∀ i, LocallyCompactSpace (E i)] : LocallyCompactSpace (Σ i, E i) := by
  refine ⟨?_⟩
  rintro ⟨i, a⟩ n hn
  obtain ⟨K, hK, hKn, hKc⟩ :=
    local_compact_nhds ((continuous_sigmaMk (σ := E) (i := i)).continuousAt hn)
  exact ⟨Sigma.mk i '' K, isOpenMap_sigmaMk.image_mem_nhds hK, Set.image_subset_iff.2 hKn,
    hKc.image continuous_sigmaMk⟩

/-- A disjoint union of metrizable spaces is metrizable. -/
theorem metrizableSpace_sigma {ι : Type*} {E : ι → Type*} [∀ i, TopologicalSpace (E i)]
    [∀ i, MetrizableSpace (E i)] : MetrizableSpace (Σ i, E i) := by
  let _ : ∀ i, MetricSpace (E i) := fun i => metrizableSpaceMetric (E i)
  let _ : MetricSpace (Σ i, E i) := Metric.Sigma.metricSpace
  infer_instance

end Sol_CGSpace_sequentialSpace_iff_exists_isQuotientMap_metrizable

open Sol_CGSpace_sequentialSpace_iff_exists_isQuotientMap_metrizable Filter in
theorem solution
    (X : Type u) [TopologicalSpace X] :
    SequentialSpace X ↔
      ∃ (M : Type u) (_ : TopologicalSpace M) (_ : MetrizableSpace M)
        (_ : LocallyCompactSpace M) (q : M → X), IsQuotientMap q := by
  constructor
  · intro hX
    -- index set: the pairs (sequence, limit of that sequence)
    let I : Type u := {p : (ℕ → X) × X // Tendsto p.1 atTop (𝓝 p.2)}
    -- on the copy of `ℕ ∪ {∞}` indexed by `(s, x)`: `n ↦ s n`, `∞ ↦ x`
    let q : (Σ _ : I, OnePoint ℕ) → X := fun z => OnePoint.elim z.2 z.1.1.2 z.1.1.1
    refine ⟨Σ _ : I, OnePoint ℕ, inferInstance, metrizableSpace_sigma,
      locallyCompactSpace_sigma, q, ?_⟩
    have hq : Continuous q := by
      refine continuous_sigma fun i => ?_
      rw [OnePoint.continuous_iff_from_nat]
      exact i.2
    refine isQuotientMap_iff_isClosed.2
      ⟨?_, fun Z => ⟨fun hZ => hZ.preimage hq, fun hZ => ?_⟩⟩
    · -- surjectivity: the point at infinity of the copy indexed by a constant sequence
      intro x
      exact ⟨⟨⟨(fun _ => x, x), tendsto_const_nhds⟩, OnePoint.infty⟩, rfl⟩
    · -- a set with closed preimage is sequentially closed, hence closed
      refine IsSeqClosed.isClosed fun s x hs hx => ?_
      let i : I := ⟨(s, x), hx⟩
      -- the inclusion of the copy indexed by `(s, x)`
      let j : OnePoint ℕ → (Σ _ : I, OnePoint ℕ) := fun a => ⟨i, a⟩
      have hj : Continuous j := continuous_sigmaMk (σ := fun _ : I => OnePoint ℕ) (i := i)
      have hc : IsClosed (j ⁻¹' (q ⁻¹' Z)) := hZ.preimage hj
      have hsub : Set.range ((↑) : ℕ → OnePoint ℕ) ⊆ j ⁻¹' (q ⁻¹' Z) := by
        rintro _ ⟨n, rfl⟩
        exact hs n
      have hmem : (OnePoint.infty : OnePoint ℕ) ∈ j ⁻¹' (q ⁻¹' Z) :=
        hc.closure_subset_iff.2 hsub (OnePoint.denseRange_coe _)
      exact hmem
  · rintro ⟨M, _, _, _, q, hq⟩
    exact hq.sequentialSpace
