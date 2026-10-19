-- Prove2me | solution 1 for CauchyRiemannIndex.exists_pos_forall_dist_lt_pair_mem
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-16T17:27:53.633666+00:00
-- url     : https://prove2.me/submissions/09536264-71be-4bba-958d-2240619e278c

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.HeineCantor



namespace CauchyRiemannIndex

/-- For a continuous map `f` on a compact pseudometric space and an open set `U` of pairs that
contains every diagonal pair `(f x, f x)`, there is a `δ > 0` such that `(f x, f y) ∈ U` whenever
`dist x y < δ`. -/
theorem exists_pos_forall_dist_lt_pair_mem_aux {X Y : Type*} [PseudoMetricSpace X] [CompactSpace X]
    [PseudoMetricSpace Y] (f : X → Y) (hf : Continuous f) (U : Set (Y × Y)) (hU : IsOpen U)
    (hfU : ∀ x, (f x, f x) ∈ U) :
    ∃ δ > 0, ∀ x y : X, dist x y < δ → (f x, f y) ∈ U := by
  have hK : IsCompact (Set.range fun x => (f x, f x)) :=
    isCompact_range (hf.prodMk hf)
  obtain ⟨ε, hε, hεU⟩ := hK.exists_thickening_subset_open hU (by
    rintro _ ⟨x, rfl⟩; exact hfU x)
  obtain ⟨δ, hδ, hδf⟩ :=
    Metric.uniformContinuous_iff.1 (CompactSpace.uniformContinuous_of_continuous hf) ε hε
  refine ⟨δ, hδ, fun x y hxy => hεU ?_⟩
  rw [Metric.mem_thickening_iff]
  refine ⟨(f x, f x), ⟨x, rfl⟩, ?_⟩
  rw [Prod.dist_eq, dist_self, dist_comm]
  exact max_lt hε (hδf hxy)

end CauchyRiemannIndex

open CauchyRiemannIndex

theorem solution {X Y : Type*} [PseudoMetricSpace X] [CompactSpace X]
    [PseudoMetricSpace Y] (f : X → Y) (hf : Continuous f) (U : Set (Y × Y)) (hU : IsOpen U)
    (hfU : ∀ x, (f x, f x) ∈ U) :
    ∃ δ > 0, ∀ x y : X, dist x y < δ → (f x, f y) ∈ U :=
  exists_pos_forall_dist_lt_pair_mem_aux f hf U hU hfU
