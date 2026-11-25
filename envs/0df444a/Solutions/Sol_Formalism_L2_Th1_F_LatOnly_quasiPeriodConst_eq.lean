-- Prove2me | solution 1 for Formalism.L2.Th1.F.LatOnly.quasiPeriodConst_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:40:26.956917+00:00
-- url     : https://prove2.me/submissions/ab4d0714-fc74-437c-b7a1-43b53c71c851

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_LatticeOnly
import Theorems.Thm_Formalism_L2_Th1_F_LatOnly_wEta_eq
import Theorems.Thm_Formalism_L2_Th1_F_LatOnly_quasiPeriodConst_formula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.LatOnly
variable {L L' : PeriodPair}
namespace Formalism.L2.Th1.F.LatOnly
theorem _root_.solution (h : L.lattice = L'.lattice) : s2 L = s2 L' := by
  rw [quasiPeriodConst_formula L, quasiPeriodConst_formula L', wEta_eq h]
end Formalism.L2.Th1.F.LatOnly
