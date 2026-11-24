-- Prove2me | solution 1 for Formalism.HN.PolygonExample.rk_Px
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:48:23.401413+00:00
-- url     : https://prove2.me/submissions/c365a6bc-9a13-423f-840a-2f970be563b5

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
theorem _root_.solution : Formalism.F.rk Px = 1 := by
  have hli : LinearIndependent ℤ ![e₀] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    fin_cases i
    have := congrArg (fun v : E2 => v 0) hg
    simpa [e₀] using this
  have hP : Px = Submodule.span ℤ (Set.range ![e₀]) := by simp [Px]
  rw [Formalism.F.rk, hP, finrank_span_eq_card hli]
  simp
end Formalism.HN.PolygonExample
