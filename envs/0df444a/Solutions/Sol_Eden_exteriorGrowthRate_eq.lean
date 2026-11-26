-- Prove2me | solution 1 for Eden.exteriorGrowthRate_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:45:35.395802+00:00
-- url     : https://prove2.me/submissions/d2621cae-faf7-45c9-a624-4ced5c8b2113

import Definitions.Def_Eden_ExteriorLimits
import Definitions.Def_Eden_SelectedSums
import Definitions.Def_Eden_KaplanYorke
import Mathlib.Topology.Order.LiminfLimsup
import Definitions.Def_Eden_ExteriorMaximalGrowth
import Theorems.Thm_Eden_tendsto_log_norm_exteriorEvolution_div


set_option autoImplicit true
noncomputable section
open Filter Set
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution {k : ℕ} (c : ℝ) (p : PhaseSpace)
    {v : ExteriorSpace k} (hv : v ≠ 0) :
    exteriorGrowthRate k c p v =
      (exteriorSupport k p v).sup' (exteriorSupport_nonempty p hv) (exteriorRate k c p) :=
  (tendsto_log_norm_exteriorEvolution_div c p hv).limUnder_eq
end Eden
