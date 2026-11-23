-- Prove2me | solution 1 for Formalism.L2.Th1.F.IsogenySigmaQuotient.ind_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:59:11.274794+00:00
-- url     : https://prove2.me/submissions/bbe1f402-ba81-4031-95a3-a074a1c373af

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_IsogenySigma

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.IsogenySigmaQuotient
variable (L : PeriodPair)
namespace Formalism.L2.Th1.F.IsogenySigmaQuotient
theorem _root_.solution {x : ℂ} (h : x ∉ L.lattice) : ind L x = 0 := by
  simp [ind, h]
end Formalism.L2.Th1.F.IsogenySigmaQuotient
