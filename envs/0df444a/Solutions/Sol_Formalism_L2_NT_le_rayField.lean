-- Prove2me | solution 1 for Formalism.L2.NT.le_rayField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:15:58.269323+00:00
-- url     : https://prove2.me/submissions/a74bc917-38af-4c22-92b1-49e2f37e871e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_RealCyclotomicTwoPower
import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_TypesDefs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Polynomial
open Formalism Formalism.L2 Formalism.L2.NT
open Formalism.L2.Host
namespace Formalism.L2.NT
theorem _root_.solution {K L : Fld} {m : ℕ} (h : RayAdm K m L) : L ≤ rayField K m :=
  le_iSup₂_of_le L h le_rfl
end Formalism.L2.NT
