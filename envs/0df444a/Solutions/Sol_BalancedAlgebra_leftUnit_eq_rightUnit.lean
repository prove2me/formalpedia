-- Prove2me | solution 1 for BalancedAlgebra.leftUnit_eq_rightUnit
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-14T15:44:35.21153+00:00
-- url     : https://prove2.me/submissions/047449cc-282c-47a7-ab95-0f8cee2ad6aa

import Mathlib
import Definitions.Def_BalancedAlgebra_core

set_option linter.unusedSectionVars false

namespace BAFix

open BalancedAlgebra BalancedAlgebra.PartialAlgebra

/-- If a left unit and a right unit are composable in that order, they coincide. -/
theorem leftUnit_eq_rightUnit {A : Type*} (P : PartialAlgebra A) (u v : A)
    (hu : P.IsLeftUnit u) (hv : P.IsRightUnit v) (huv : P.IsDefined u v) : u = v := by
  obtain ⟨x, hx⟩ := huv
  exact (hv u x hx).symm.trans (hu v x hx)

end BAFix

open BalancedAlgebra BalancedAlgebra.PartialAlgebra in
theorem solution {A : Type*} (P : PartialAlgebra A) (u v : A)
    (hu : P.IsLeftUnit u) (hv : P.IsRightUnit v) (huv : P.IsDefined u v) : u = v :=
  BAFix.leftUnit_eq_rightUnit P u v hu hv huv
