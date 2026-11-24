-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.norm_singular_value_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:45.549801+00:00
-- url     : https://prove2.me/submissions/8c68db8f-72a7-47e7-b295-5fdc06d99842

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MinkowskiNumberDvdFactorial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.S6.NormSgBound := by
  intro ι _ r f D sg H₁ Hh hf hH hHh hD0 hsg hD
  have hp0 : (0:ℝ) < (2 * H₁) ^ (2 * r) := by
    have : (0:ℝ) < 2 * H₁ := by linarith
    positivity
  have h1 : ∀ v, D v ≤ (2 * H₁) ^ (2 * r) * sg v := fun v => by
    have := hD v
    rw [div_le_iff₀ hp0] at this; rw [mul_comm]; exact this
  calc ∏ v, D v ^ 2 ≤ ∏ v, ((2 * H₁) ^ (2 * r) * sg v) ^ 2 :=
        Finset.prod_le_prod (fun v _ => by positivity) (fun v _ => pow_le_pow_left₀ (hD0 v) (h1 v) 2)
    _ = (2 * H₁) ^ (4 * r * f) * ∏ v, sg v ^ 2 := by
        simp_rw [mul_pow]
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hf, ← pow_mul, ← pow_mul]
        congr 2; ring
    _ ≤ Hh * ∏ v, sg v ^ 2 := by
        apply mul_le_mul_of_nonneg_right hHh
        exact Finset.prod_nonneg (fun v _ => by positivity)
end Formalism.HermitianLatticeCounting.P
