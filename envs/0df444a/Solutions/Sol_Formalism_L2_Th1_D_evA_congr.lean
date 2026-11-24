-- Prove2me | solution 1 for Formalism.L2.Th1.D.evA_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:17:56.002303+00:00
-- url     : https://prove2.me/submissions/fc927a33-c924-4650-9426-50028910fadd

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_RingAFacts
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_FrobeniusOnRingA
import Theorems.Thm_Formalism_L2_Th1_D_evA_of
import Theorems.Thm_Formalism_L2_Th1_D_int_fermat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
variable (l : ℕ) [Fact l.Prime]
namespace Formalism.L2.Th1.D
theorem _root_.solution (r : MonoidAlgebra ℤ (muSub l)) :
    ∃ y : ringA l, evA l l r - evA l 1 r ^ l = (l : ringA l) * y := by
  induction r using MonoidAlgebra.induction_on with
  | of g =>
    refine ⟨0, ?_⟩
    rw [evA_of, evA_of, pow_one, sub_self, mul_zero]
  | add x y hx hy =>
    obtain ⟨u, hu⟩ := hx
    obtain ⟨v, hv⟩ := hy
    obtain ⟨w, hw⟩ := exists_add_pow_prime_eq (Fact.out : l.Prime) (evA l 1 x) (evA l 1 y)
    refine ⟨u + v - evA l 1 x * evA l 1 y * w, ?_⟩
    rw [map_add, map_add, hw]
    linear_combination hu + hv
  | smul a x hx =>
    obtain ⟨u, hu⟩ := hx
    obtain ⟨c, hc⟩ := int_fermat l a
    have hc' : (a : ringA l) - (a : ringA l) ^ l = (l : ringA l) * (c : ringA l) := by
      exact_mod_cast congrArg (Int.cast : ℤ → ringA l) hc
    refine ⟨(a : ringA l) * u + (c : ringA l) * evA l 1 x ^ l, ?_⟩
    rw [zsmul_eq_mul, map_mul, map_mul, map_intCast, map_intCast, mul_pow]
    linear_combination (a : ringA l) * hu + (evA l 1 x ^ l) * hc'
end Formalism.L2.Th1.D
