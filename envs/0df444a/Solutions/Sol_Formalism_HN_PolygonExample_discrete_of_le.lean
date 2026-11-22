-- Prove2me | solution 1 for Formalism.HN.PolygonExample.discrete_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:34:41.269728+00:00
-- url     : https://prove2.me/submissions/f2741c83-8283-41b9-bb79-8fa91ec7c9cd

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNSlopes
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Example
import Theorems.Thm_Formalism_HN_PolygonExample_one_le_norm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.HN
open Formalism.HN.PolygonExample
namespace Formalism.HN.PolygonExample
theorem _root_.solution (N : Submodule ℤ E2) (hN : N ≤ Lx) : DiscreteTopology N := by
  refine discreteTopology_of_isOpen_singleton_zero
    (Metric.isOpen_singleton_iff.2 ⟨1, one_pos, fun y hy => ?_⟩)
  by_contra hne
  have hy0 : (y : E2) ≠ 0 := fun h => hne (Subtype.ext h)
  have := one_le_norm (hN y.2) hy0
  rw [dist_zero_right, Submodule.coe_norm] at hy
  linarith
end Formalism.HN.PolygonExample
