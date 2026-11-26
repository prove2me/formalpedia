-- Prove2me | solution 1 for Eden.finiteTimeDimension_isGreatest
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:04:41.703799+00:00
-- url     : https://prove2.me/submissions/da8d4f05-3e0f-48d3-a233-3b851bd82024

import Definitions.Def_Eden_SingularValues
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.Compact
import Definitions.Def_Eden_SingularValueFunction
import Theorems.Thm_Eden_mapLyapunovDimension_isGreatest
import Theorems.Thm_Eden_fderiv_evolution_bijective


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace) :
    IsGreatest (admissibleDimensions (fderiv ℝ (evolution c t) p).toLinearMap)
      (finiteTimeDimension c t p) :=
  mapLyapunovDimension_isGreatest (fderiv_evolution_bijective c ht p).injective
end Eden
