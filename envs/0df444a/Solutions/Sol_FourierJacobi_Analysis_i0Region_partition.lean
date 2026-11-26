-- Prove2me | solution 1 for FourierJacobi.Analysis.i0Region_partition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:22:39.84813+00:00
-- url     : https://prove2.me/submissions/bde1c1a7-5f92-4160-8180-0f6ad2da6684

import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Definitions.Def_FourierJacobi_Analysis_I0Complete
import Theorems.Thm_FourierJacobi_Analysis_i0RegionIndex_mem
import Theorems.Thm_FourierJacobi_Analysis_i0Region_unique

set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace FourierJacobi.Analysis
theorem _root_.solution (p : ℤ × ℤ × ℤ) : ∃! i : Fin 10, p ∈ i0Region i :=
  ⟨i0RegionIndex p, i0RegionIndex_mem p, fun i hi =>
    i0Region_unique p i (i0RegionIndex p) hi (i0RegionIndex_mem p)⟩
end FourierJacobi.Analysis
