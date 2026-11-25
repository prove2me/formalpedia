-- Prove2me | solution 1 for Formalism.L2.SG.GGMirabolic.Inhab.regular_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:11:46.170161+00:00
-- url     : https://prove2.me/submissions/dc9bf74c-d8c6-4729-ad39-4996a205f99c

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolicInhab

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.GGMirabolic Formalism.L2.SG.GGMirabolic.Inhab
open Formalism.L2.SG.GGMirabolic
noncomputable section
open Classical
namespace Formalism.L2.SG.GGMirabolic.Inhab
theorem _root_.solution {G : Type} [Group G] (i j : G) : MulOpposite.op (j⁻¹ * i) • j = i := by
  rw [MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, mul_inv_cancel_left]
end Formalism.L2.SG.GGMirabolic.Inhab
