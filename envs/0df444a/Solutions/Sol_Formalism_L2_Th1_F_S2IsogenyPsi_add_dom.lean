-- Prove2me | solution 1 for Formalism.L2.Th1.F.S2IsogenyPsi.add_dom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:28:38.825278+00:00
-- url     : https://prove2.me/submissions/8b974499-ac5a-477b-b29d-5266f72a6792

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
theorem _root_.solution {L : PeriodPair} {α z P : ℂ} (hP : α * P ∈ L.lattice) (hz : α * z ∉ L.lattice) :
    α * (z + P) ∉ L.lattice := by
  intro h
  apply hz
  have e : α * z = α * (z + P) - α * P := by ring
  rw [e]
  exact L.lattice.sub_mem h hP
end Formalism.L2.Th1.F.S2IsogenyPsi
