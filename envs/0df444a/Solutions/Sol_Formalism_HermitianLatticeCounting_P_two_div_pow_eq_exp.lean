-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.two_div_pow_eq_exp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:12:35.431847+00:00
-- url     : https://prove2.me/submissions/48eb52ba-b252-4f13-87e3-4a9fd691d648

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExponentInequalityNondegenerateMid
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_pow_eq_exp_mul_log

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (g : ℝ) (hg : 0 < g) (n : ℕ) :
    (2 / g) ^ n = Real.exp ((n:ℝ) * (Real.log 2 - Real.log g)) := by
  rw [pow_eq_exp_mul_log _ (div_pos two_pos hg) n, Real.log_div (by norm_num) hg.ne']
end Formalism.HermitianLatticeCounting.P
