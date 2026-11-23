-- Prove2me | solution 1 for Formalism.L2.Pj.isGenFr_genFr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:57:27.550805+00:00
-- url     : https://prove2.me/submissions/d49095db-57c8-4196-a91d-129a47c3f201

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsCombAt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsGenFrGenFr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l)
variable {Xo c}
namespace Formalism.L2.Pj
theorem _root_.solution (h : GenFrEx Xo c) (Z : Comp Xo c) : IsGenFr Z (genFr h Z) := (h Z).choose_spec
end Formalism.L2.Pj
