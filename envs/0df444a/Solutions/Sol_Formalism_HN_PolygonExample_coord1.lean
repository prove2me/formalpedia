-- Prove2me | solution 1 for Formalism.HN.PolygonExample.coord1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:08:14.122953+00:00
-- url     : https://prove2.me/submissions/f29b9bd9-3f81-45f0-b0df-6c3c0eba6e72

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
theorem _root_.solution (m n : ℤ) : (m • e₀ + n • ((2 : ℝ) • e₁)) 1 = 2 * n := by
  simp [e₀, e₁]
  ring
end Formalism.HN.PolygonExample
