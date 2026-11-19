-- Prove2me | solution 1 for DeletionCode.RandomHash.rational_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:43:02.892234+00:00
-- url     : https://prove2.me/submissions/a4d7a3bb-a4b4-419a-a49e-d7f2cfdaebce

import Definitions.Def_DeletionCode_IntegerTorusMap
import Definitions.Def_DeletionCode_TorusHaar
import Definitions.Def_DeletionCode_CircleUniform
import Definitions.Def_DeletionCode_RandomHash

set_option autoImplicit true
open DeletionCode DeletionCode.RandomHash
open MeasureTheory ProbabilityTheory CircleHash IntegerTorusMap CircleUniform
open scoped BigOperators
variable {I J : Type*} [Fintype I] [Fintype J]
omit [Fintype I]
namespace DeletionCode.RandomHash
theorem _root_.solution (w : I → ℤ) (hw : w ≠ 0) : (fun i => (w i : ℚ)) ≠ 0 := by
  intro h
  apply hw
  funext i
  have hi := congrFun h i
  change (w i : ℚ) = 0 at hi
  change w i = 0
  exact_mod_cast hi
end DeletionCode.RandomHash
