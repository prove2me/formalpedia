-- Prove2me | solution 1 for Formalism.L2.Th1.F.LegendreModelEllipticTorsion.summable_e2Summand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:52:59.686951+00:00
-- url     : https://prove2.me/submissions/c3a3a553-2365-4078-92be-f8db5e206e73

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Legendre
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Legendre
import Theorems.Thm_Formalism_L2_Th1_F_LegendreModelEllipticTorsion_summable_e2Summand_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open UpperHalfPlane hiding I
open EisensteinSeries Complex SummationFilter ModularGroup
open scoped Real
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F Formalism.L2.Th1.F.LegendreModelEllipticTorsion
namespace Formalism.L2.Th1.F.LegendreModelEllipticTorsion
theorem _root_.solution (z : ℍ) : Summable fun n : ℤ => e2Summand n z := by
  have hev := EisensteinSeries.e2Summand_even z
  have h0 : Summable fun n : ℕ => e2Summand (n : ℤ) z := by
    rw [← summable_nat_add_iff 1]
    refine (summable_e2Summand_succ z).congr ?_
    intro a
    push_cast
    rfl
  refine Summable.of_nat_of_neg h0 ?_
  refine h0.congr ?_
  intro n
  exact (hev (n : ℤ)).symm
end Formalism.L2.Th1.F.LegendreModelEllipticTorsion
