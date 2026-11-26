-- Prove2me | solution 1 for FourierJacobi.Algebra.weyl_target_numerator_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:19:12.160721+00:00
-- url     : https://prove2.me/submissions/1fc6fa7e-43fb-4697-a231-f71b3e72db54

import Definitions.Def_FourierJacobi_Algebra_WeylSum
import Definitions.Def_FourierJacobi_Algebra_WeylEvaluation

set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra
variable {K : Type*} [Field K]
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
namespace FourierJacobi.Algebra
theorem _root_.solution (t a b d : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    weylTargetNumerator t a b d =
      (weylWall a b * a ^ 2 * b ^ 2 * d * (a ^ 2 * b ^ 2 * d ^ 4)) *
        (satakeNumerator a b * (1 - t ^ 2) * n₁ t a b * n₂ t a b) := by
  unfold weylTargetNumerator weylWall satakeNumerator n₁ n₂ fourFactors
  field_simp
  ring
end FourierJacobi.Algebra
