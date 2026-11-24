-- Prove2me | solution 1 for Formalism.HN.ex_slope
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:23.288022+00:00
-- url     : https://prove2.me/submissions/8b2b9302-638c-4c06-8024-dd4d1b0fe029

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNSlopes
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Example
import Theorems.Thm_Formalism_HN_PolygonExample_zl_id

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
open PolygonExample
local notation "ρx" => AddMonoidHom.id E2
namespace Formalism.HN
theorem _root_.solution (N : Submodule ℤ E2) : slope ρx N = Formalism.F.slope N := by
  simp only [Formalism.HN.slope, zl_id]
end Formalism.HN
