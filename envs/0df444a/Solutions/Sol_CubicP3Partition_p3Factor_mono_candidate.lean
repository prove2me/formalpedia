-- Prove2me | solution 1 for CubicP3Partition.p3Factor_mono_candidate
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T01:03:44.301134+00:00
-- url     : https://prove2.me/submissions/d3bb3706-7d50-4609-a42f-4d2b78046962

import Definitions.Def_cubic_p3_partition_models

namespace CubicP3Partition

universe u


end CubicP3Partition

open CubicP3Partition
universe u
theorem solution
    {V : Type u} [Fintype V] [DecidableEq V]
    {G H : SimpleGraph V} (hGH : G ≤ H) :
    Nonempty (P3Factor G) → Nonempty (P3Factor H) := by
  intro hFactor
  obtain ⟨p⟩ := hFactor
  refine ⟨{
    blockCount := p.blockCount
    place := p.place
    edge01 := ?_
    edge12 := ?_
  }⟩
  · intro i
    exact hGH (p.edge01 i)
  · intro i
    exact hGH (p.edge12 i)

