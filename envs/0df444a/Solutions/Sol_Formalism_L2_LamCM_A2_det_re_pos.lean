-- Prove2me | solution 1 for Formalism.L2.LamCM.A2.det_re_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:03:37.067818+00:00
-- url     : https://prove2.me/submissions/232cd96f-fdc2-4dc7-a8d1-98633757b888

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementA
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ProdMulLeDetIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open NumberField IsDedekindDomain
open scoped nonZeroDivisors ComplexOrder
open Formalism.L2.LamCM.A2
variable {K : Type} [Field K] [NumberField K]
namespace Formalism.L2.LamCM.A2
theorem _root_.solution {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (h : A.PosDef) : 0 < A.det.re := by
  simpa using (Complex.lt_def.1 h.det_pos).1
end Formalism.L2.LamCM.A2
