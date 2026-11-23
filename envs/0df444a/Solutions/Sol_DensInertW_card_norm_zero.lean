-- Prove2me | solution 1 for DensInertW.card_norm_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:52:27.16981+00:00
-- url     : https://prove2.me/submissions/17628fc3-e524-4cb3-a9b5-fc6648c72dd4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_ExistsTraceNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
open DensInertW
variable {K L : Type} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]
omit [Fintype K] [Algebra K L]
namespace DensInertW
theorem _root_.solution [DecidableEq L] (n : ℕ) : #{x : L | x ^ (n + 1) = 0} = 1 := by
  rw [card_eq_one]
  refine ⟨0, ?_⟩
  ext x
  simp
end DensInertW
