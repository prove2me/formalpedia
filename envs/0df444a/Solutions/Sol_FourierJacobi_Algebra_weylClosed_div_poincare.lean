-- Prove2me | solution 1 for FourierJacobi.Algebra.weylClosed_div_poincare
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:19:34.159889+00:00
-- url     : https://prove2.me/submissions/e746c277-22f5-4115-bfcf-af4cb145c18c

import Definitions.Def_FourierJacobi_Algebra_WeylSum
import Definitions.Def_FourierJacobi_Algebra_WeylEvaluation

set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra
variable {K : Type*} [Field K]
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
namespace FourierJacobi.Algebra
theorem _root_.solution (t a b d : K) :
    weylClosedExpression t a b d / poincare t = closedCore t a b d := by
  unfold weylClosedExpression closedCore
  rw [div_div]
  congr 1
  ring
end FourierJacobi.Algebra
