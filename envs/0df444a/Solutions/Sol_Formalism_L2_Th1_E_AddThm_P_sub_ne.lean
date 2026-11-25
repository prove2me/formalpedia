-- Prove2me | solution 1 for Formalism.L2.Th1.E.AddThm.P_sub_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:08:51.292115+00:00
-- url     : https://prove2.me/submissions/7c6057d0-d0ff-4373-9966-d0c041f261e5

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ExistsFinitePartOneIdeleSplitCongruenceQuotient
import Theorems.Thm_Formalism_L2_Th1_F_pInjective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.E
open Formalism.L2.Th1.E.AddThm
open Formalism.L2.Th1
variable (L : PeriodPair)
namespace Formalism.L2.Th1.E.AddThm
theorem _root_.solution (z w : ℂ) (hz : z ∉ L.lattice) (hw : w ∉ L.lattice) (hp : z + w ∉ L.lattice)
    (hm : z - w ∉ L.lattice) : L.weierstrassP z - L.weierstrassP w ≠ 0 := by
  intro h
  rcases (Formalism.L2.Th1.F.pInjective L z w hz hw).mp (sub_eq_zero.mp h) with h1 | h1
  · exact hm h1
  · exact hp h1
end Formalism.L2.Th1.E.AddThm
