-- Prove2me | solution 1 for Formalism.L2.Pj.CompFin.quasiCompact_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:22:06.166801+00:00
-- url     : https://prove2.me/submissions/1ab84734-6000-4e49-b329-83ca343b8f6a

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsGenFrGenFr
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompFin
import Theorems.Thm_Formalism_L2_Pj_CompFin_quasiCompact_str

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
theorem _root_.solution (Xo : Moduli Dw l) : QuasiCompact Xo.s := by
  obtain ⟨N, i, -, hq, h⟩ := Xo.qproj
  haveI := hq
  haveI := quasiCompact_str (KA l) N
  rw [← h]
  infer_instance
end Formalism.L2.Pj.CompFin
