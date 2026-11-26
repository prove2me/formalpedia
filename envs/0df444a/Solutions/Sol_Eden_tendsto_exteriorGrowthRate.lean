-- Prove2me | solution 1 for Eden.tendsto_exteriorGrowthRate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:46:49.745863+00:00
-- url     : https://prove2.me/submissions/dc40973c-88b7-4223-b9af-3b440ea45a6b

import Definitions.Def_Eden_ExteriorLimits
import Definitions.Def_Eden_SelectedSums
import Definitions.Def_Eden_KaplanYorke
import Mathlib.Topology.Order.LiminfLimsup
import Definitions.Def_Eden_ExteriorMaximalGrowth
import Theorems.Thm_Eden_exteriorGrowthRate_eq
import Theorems.Thm_Eden_tendsto_log_norm_exteriorEvolution_div


set_option autoImplicit true
noncomputable section
open Filter Set
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution {k : ℕ} (c : ℝ) (p : PhaseSpace)
    {v : ExteriorSpace k} (hv : v ≠ 0) :
    Tendsto (fun t => Real.log ‖exteriorEvolution k c t p v‖ / t) atTop
      (𝓝 (exteriorGrowthRate k c p v)) := by
  rw [exteriorGrowthRate_eq c p hv]
  exact tendsto_log_norm_exteriorEvolution_div c p hv
end Eden
