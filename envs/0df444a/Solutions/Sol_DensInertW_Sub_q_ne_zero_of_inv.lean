-- Prove2me | solution 1 for DensInertW.Sub.q_ne_zero_of_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:26:01.930829+00:00
-- url     : https://prove2.me/submissions/a31cb348-e860-4a6a-b6eb-0c93da9e5d87

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_AnisoPeelAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_FinrankInfKerAddOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Module
open DensInertW DensInertW.Sub
variable {L : Type} [Field L]
namespace DensInertW.Sub
theorem _root_.solution {q : ℕ} (hinv : ∀ a : L, (a ^ q) ^ q = a) : q ≠ 0 := by
  intro hq
  subst hq
  have h := hinv 0
  simp at h
end DensInertW.Sub
