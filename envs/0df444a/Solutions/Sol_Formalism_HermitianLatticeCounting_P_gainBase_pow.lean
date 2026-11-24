-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.gainBase_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:48.857139+00:00
-- url     : https://prove2.me/submissions/a06bb273-b873-42ff-9252-bf4d2030cc39

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
theorem _root_.solution (k r : ℕ) (C ν t g : ℝ) (hk : 1 ≤ k) (hC : 0 < C) :
    (xv k r C ν t g) ^ k =
      ν ^ k * t ^ k * (g⁻¹ ^ (2 * r + 2)) ^ k * (C / k) ^ (2 * r * (k - 2 - r)) := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.xv Formalism.HermitianLatticeCounting.LatticeSumBounds.expo
  rw [mul_pow, mul_pow, mul_pow,
    ← Real.rpow_natCast ((C / (k:ℝ)) ^ (((2 * r * (k - 2 - r) : ℕ) : ℝ) / (k:ℝ))) k,
    ← Real.rpow_mul (by positivity), div_mul_cancel₀ _ hk0.ne', Real.rpow_natCast]
end Formalism.HermitianLatticeCounting.P
