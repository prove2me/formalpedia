-- Prove2me | solution 1 for Formalism.LogFactorialMertensBounds.Icc_one_eq_Ioc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:38:22.089899+00:00
-- url     : https://prove2.me/submissions/d84b88eb-1088-43c8-b140-24090484fab6

import Definitions.Def_Formalism_StatementU
import Definitions.Def_Formalism_ZetaNonvanishing_GzLipschitz

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
theorem _root_.solution (k : ℕ) : Finset.Icc 1 k = Finset.Ioc 0 k := by
  ext n
  simp only [Finset.mem_Icc, Finset.mem_Ioc]
  omega
end Formalism.LogFactorialMertensBounds
