-- Prove2me | solution 1 for Formalism.L2.Pj.dualMap_eps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:16:44.247977+00:00
-- url     : https://prove2.me/submissions/f4bb3acf-bd85-485a-a986-21a4b0dea833

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnitIndepOfCharts
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open MonObj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}
namespace Formalism.L2.Pj
theorem _root_.solution {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) (a : S) :
    (dualMap φ).comp (epsMul a) = (epsMul (φ a)).comp (dualMap φ) :=
  RingHom.ext fun x => by
    ext <;> simp [dualMap, epsMul, mul_comm]
end Formalism.L2.Pj
