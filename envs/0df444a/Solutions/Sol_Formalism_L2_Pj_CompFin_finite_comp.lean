-- Prove2me | solution 1 for Formalism.L2.Pj.CompFin.finite_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:49:35.589421+00:00
-- url     : https://prove2.me/submissions/3e2a01c9-68f0-4d5d-9059-26c380e2853e

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsGenFrGenFr
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompFin
import Theorems.Thm_Formalism_L2_Pj_CompFin_isNoetherian_XF

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.CompFin
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] MvPolynomial.gradedAlgebra
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
namespace Formalism.L2.Pj.CompFin
theorem _root_.solution (Xo : Moduli Dw l) (c : Coeff l) : Finite (Comp Xo c) := by
  haveI := isNoetherian_XF Xo c
  exact TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.to_subtype
end Formalism.L2.Pj.CompFin
