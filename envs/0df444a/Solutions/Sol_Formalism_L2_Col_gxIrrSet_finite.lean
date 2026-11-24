-- Prove2me | solution 1 for Formalism.L2.Col.gxIrrSet_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:11:50.222816+00:00
-- url     : https://prove2.me/submissions/f90fdbd1-899a-4ee7-9d60-92871cc421d1

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Columns_GoodXgFin
import Theorems.Thm_Formalism_L2_Col_gx_linInd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Col
open Formalism.L2.DIV
variable {G : Type} [Group G] [Fintype G]
namespace Formalism.L2.Col
theorem _root_.solution {k : Type} [Field k] [IsAlgClosed k] [CharZero k] : (gxIrrSet (G := G) k).Finite := Set.finite_coe_iff.1 (gx_linInd (G := G) (k := k)).finite
end Formalism.L2.Col
