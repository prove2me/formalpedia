-- Prove2me | solution 1 for Formalism.HN.PolygonExample.covol_Px
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:15.28618+00:00
-- url     : https://prove2.me/submissions/7eec5811-daec-442b-9d8a-09ef21c292fc

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNSlopes
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Example
import Theorems.Thm_P2M_Formalism_HN_PolygonExample_e__ne_bc6b4793aac7
import Theorems.Thm_Formalism_F_covolBasic


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
theorem _root_.solution : Formalism.F.covol Px = 1 := by
  exact (Formalism.F.covolBasic E2).2 e₀ e₀_ne |>.trans (by simp [e₀])
end Formalism.HN.PolygonExample
