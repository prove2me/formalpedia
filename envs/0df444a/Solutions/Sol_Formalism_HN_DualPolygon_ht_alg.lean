-- Prove2me | solution 1 for Formalism.HN.DualPolygon.ht_alg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:13.838878+00:00
-- url     : https://prove2.me/submissions/f94e67dd-18f0-4ecd-81c7-48915b5efcf5

import Definitions.Def_Formalism_HarderNarasimhan_QuotRealize
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Duality
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.HN Formalism.HN.DualPolygon
open Formalism.HN
namespace Formalism.HN.DualPolygon
theorem _root_.solution (f r j : ℕ) (D u cR cL cS : ℝ) (hu : u ^ 2 * D = 1)
    (h : cR * cL * 2 ^ (2 * f * r) = D ^ r * cS) :
    2 ^ (f * r) * u ^ r * cR * (2 ^ (f * (r + j)) * u ^ (r + j) * cL) =
      2 ^ (f * j) * u ^ j * cS := by
  calc 2 ^ (f * r) * u ^ r * cR * (2 ^ (f * (r + j)) * u ^ (r + j) * cL)
      = 2 ^ (f * j) * u ^ j * (u ^ 2) ^ r * (cR * cL * 2 ^ (2 * f * r)) := by ring
    _ = 2 ^ (f * j) * u ^ j * (u ^ 2 * D) ^ r * cS := by rw [h]; ring
    _ = _ := by rw [hu, one_pow, mul_one]
end Formalism.HN.DualPolygon
