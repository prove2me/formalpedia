-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.powLeMaxMulMax
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:59:19.830485+00:00
-- url     : https://prove2.me/submissions/3b0dc1ee-c32d-421b-9a99-067ac85a1d58

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds

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
theorem _root_.solution : BlockScalarBound := by
  intro t x y s c ht hx hy hcs hts
  have hM : 1 ≤ max 1 x * max 1 (1 / y) :=
    one_le_mul_of_one_le_of_one_le (le_max_left _ _) (le_max_left _ _)
  rcases le_or_gt 1 t with h1 | h1
  · calc t ^ c ≤ t ^ s := pow_le_pow_right₀ h1 hcs
      _ = x * (1 / y) := by rw [hts, div_eq_mul_one_div]
      _ ≤ max 1 x * max 1 (1 / y) :=
          mul_le_mul (le_max_right _ _) (le_max_right _ _) (by positivity)
            (zero_le_one.trans (le_max_left _ _))
  · calc t ^ c ≤ 1 := pow_le_one₀ ht.le h1.le
      _ ≤ _ := hM
end Formalism.HermitianLatticeCounting.P
