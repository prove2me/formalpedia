-- Prove2me | solution 1 for FourierJacobi.Algebra.clearedExpansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:30:25.06788+00:00
-- url     : https://prove2.me/submissions/41b1cbf6-6f5e-4cb6-b5a8-f726e9d62666

import Definitions.Def_FourierJacobi_Algebra_WeylCoefficient10
import Definitions.Def_FourierJacobi_Algebra_WeylSum
import Theorems.Thm_FourierJacobi_Algebra_clearedExpansion0
import Theorems.Thm_FourierJacobi_Algebra_clearedExpansion1
import Theorems.Thm_FourierJacobi_Algebra_clearedExpansion2
import Theorems.Thm_FourierJacobi_Algebra_clearedExpansion3
import Theorems.Thm_FourierJacobi_Algebra_clearedExpansion4
import Theorems.Thm_FourierJacobi_Algebra_clearedExpansion5
import Theorems.Thm_FourierJacobi_Algebra_clearedExpansion6
import Theorems.Thm_FourierJacobi_Algebra_clearedExpansion7


set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra
variable {K : Type*} [Field K]
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace FourierJacobi.Algebra
theorem _root_.solution (t a b d : K) (i : Fin 8) :
    weylClearedTerms t a b d i = evalCoefficients d (allWeylCoefficients t a b i) := by
  fin_cases i
  · exact clearedExpansion0 t a b d
  · exact clearedExpansion1 t a b d
  · exact clearedExpansion2 t a b d
  · exact clearedExpansion3 t a b d
  · exact clearedExpansion4 t a b d
  · exact clearedExpansion5 t a b d
  · exact clearedExpansion6 t a b d
  · exact clearedExpansion7 t a b d
end FourierJacobi.Algebra
