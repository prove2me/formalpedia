-- Prove2me | solution 1 for Formalism.LogFactorialMertensBounds.Gz_eq_P
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:52:55.817528+00:00
-- url     : https://prove2.me/submissions/e49a9d4e-b1fc-42f9-874a-94e35569c39c

import Definitions.Def_Formalism_StatementU
import Definitions.Def_Formalism_ZetaNonvanishing_GzLipschitz
import Theorems.Thm_Formalism_LogFactorialMertensBounds_Sz_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ArithmeticFunction
noncomputable section
open Formalism
open Formalism.LogFactorialMertensBounds
namespace Formalism.LogFactorialMertensBounds
theorem _root_.solution (k : ℕ) (x : ℝ) (hx1 : (k:ℝ) ≤ x) (hx2 : x ≤ k + 1) : Gz x = P k x := by
  unfold Gz P
  rw [Sz_eq k x hx1 hx2]
end Formalism.LogFactorialMertensBounds
