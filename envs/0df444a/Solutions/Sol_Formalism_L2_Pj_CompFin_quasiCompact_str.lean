-- Prove2me | solution 1 for Formalism.L2.Pj.CompFin.quasiCompact_str
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:14:45.554637+00:00
-- url     : https://prove2.me/submissions/0a1fdbe5-9b3e-4f82-8afd-0302916994da

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsGenFrGenFr
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompFin
import Theorems.Thm_Formalism_L2_Pj_CompFin_finiteType_zero

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
namespace Formalism.L2.Pj.CompFin
theorem _root_.solution (R : Type) [CommRing R] (N : ℕ) : QuasiCompact (PSpace.str R N) := by
  haveI := finiteType_zero R N
  unfold PSpace.str
  infer_instance
end Formalism.L2.Pj.CompFin
