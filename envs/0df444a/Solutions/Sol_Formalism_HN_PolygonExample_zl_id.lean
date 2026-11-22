-- Prove2me | solution 1 for Formalism.HN.PolygonExample.zl_id
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:08:14.156682+00:00
-- url     : https://prove2.me/submissions/f32aef1c-481c-463a-a964-e5ef8e6b4610

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNSlopes
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Example

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
theorem _root_.solution (N : Submodule ℤ E2) : zl (AddMonoidHom.id E2) N = N := by
  ext x
  simp [zl]
end Formalism.HN.PolygonExample
