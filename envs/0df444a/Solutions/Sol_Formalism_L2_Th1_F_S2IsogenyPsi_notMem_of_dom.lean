-- Prove2me | solution 1 for Formalism.L2.Th1.F.S2IsogenyPsi.notMem_of_dom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:28:49.500472+00:00
-- url     : https://prove2.me/submissions/a88008fa-3a60-441c-86cd-30664e61bb6c

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_QuasiPeriodConstIsogeny

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
open Formalism.L2.Th1.F.S2IsogenyPsi
namespace Formalism.L2.Th1.F.S2IsogenyPsi
theorem _root_.solution {L : PeriodPair} {α z : ℂ} (hst : MulStable L α) (hz : α * z ∉ L.lattice) :
    z ∉ L.lattice := fun hz' => hz (hst z hz')
end Formalism.L2.Th1.F.S2IsogenyPsi
