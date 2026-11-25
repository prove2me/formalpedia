-- Prove2me | solution 1 for Formalism.L2.Pj.intFrames
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:06:35.765588+00:00
-- url     : https://prove2.me/submissions/d3b4a1ab-bb77-4ee1-b66d-bbf78505c5a4

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_VAtVNeBot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntFrames
import Theorems.Thm_Formalism_L2_Pj_genFibre
import Theorems.Thm_Formalism_L2_Pj_intFrames_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)
namespace Formalism.L2.Pj
theorem _root_.solution (hC : ReciprocityTheory.ChartRestriction.G.Out.CubePullSt) (hL : LieFreeSt Xo c) (hT : ThetaFrameSt Xo c)
    (hS : SpreadSt Xo c) : IntFramesSt Xo c :=
  intFrames_of Xo c hC (genFibre Xo c hC) hL hT hS
end Formalism.L2.Pj
