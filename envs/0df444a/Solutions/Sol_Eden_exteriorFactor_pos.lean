-- Prove2me | solution 1 for Eden.exteriorFactor_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:32:58.777798+00:00
-- url     : https://prove2.me/submissions/b97cf4ab-5d05-42c7-803e-2d745aeece2c

import Definitions.Def_Eden_ExteriorGeometry
import Definitions.Def_Eden_LogarithmicSums
import Definitions.Def_Eden_FactorLimits
import Definitions.Def_Eden_ExteriorLimits
import Theorems.Thm_Eden_derivativeFactors_pos


set_option autoImplicit true
noncomputable section
open Filter Set
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution (k : ℕ) (c : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (p : PhaseSpace) (s : ExteriorIndex k) :
    0 < exteriorFactor k (derivativeFactors c t p) s :=
  Finset.prod_pos (fun _ _ => derivativeFactors_pos c ht p _)
end Eden
