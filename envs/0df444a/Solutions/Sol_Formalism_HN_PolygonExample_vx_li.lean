-- Prove2me | solution 1 for Formalism.HN.PolygonExample.vx_li
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:56:17.855555+00:00
-- url     : https://prove2.me/submissions/59139777-5d05-4956-a0b4-ab44ccea49bb

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNSlopes
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Example
import Theorems.Thm_Formalism_HN_PolygonExample_coord0
import Theorems.Thm_Formalism_HN_PolygonExample_coord1

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
theorem _root_.solution : LinearIndependent ℤ vx := by
  unfold vx
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h0 := congrArg (fun v : E2 => v 0) hst
  have h1 := congrArg (fun v : E2 => v 1) hst
  simp only [coord0, coord1] at h0 h1
  simp only [PiLp.zero_apply] at h0 h1
  constructor
  · exact_mod_cast h0
  · have : (t : ℝ) = 0 := by linarith
    exact_mod_cast this
end Formalism.HN.PolygonExample
