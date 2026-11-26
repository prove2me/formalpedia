-- Prove2me | solution 1 for Eden.limsup_exteriorGrowthRate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:12:43.883867+00:00
-- url     : https://prove2.me/submissions/8ee76f65-ec22-41f2-942f-00785b8a1fe5

import Definitions.Def_Eden_ExteriorLimits
import Definitions.Def_Eden_SelectedSums
import Definitions.Def_Eden_KaplanYorke
import Mathlib.Topology.Order.LiminfLimsup
import Definitions.Def_Eden_ExteriorMaximalGrowth
import Theorems.Thm_Eden_tendsto_exteriorGrowthRate

set_option autoImplicit true
noncomputable section
open Filter Set
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution {k : ℕ} (c : ℝ) (p : PhaseSpace)
    {v : ExteriorSpace k} (hv : v ≠ 0) :
    limsup (fun t => Real.log ‖exteriorEvolution k c t p v‖ / t) atTop =
      exteriorGrowthRate k c p v :=
  (tendsto_exteriorGrowthRate c p hv).limsup_eq
end Eden
