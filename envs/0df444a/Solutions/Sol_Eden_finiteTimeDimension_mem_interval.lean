-- Prove2me | solution 1 for Eden.finiteTimeDimension_mem_interval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:06:24.835838+00:00
-- url     : https://prove2.me/submissions/1838625a-f8af-4842-94fc-10760302fb24

import Definitions.Def_Eden_SingularValues
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.Compact
import Definitions.Def_Eden_SingularValueFunction
import Theorems.Thm_Eden_finiteTimeDimension_isGreatest

set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace) :
    finiteTimeDimension c t p ∈ Icc 0 5 := (finiteTimeDimension_isGreatest c ht p).1.1
end Eden
