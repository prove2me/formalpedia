-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.le_exp_mul_of_near_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:51:37.798166+00:00
-- url     : https://prove2.me/submissions/ca29a92b-7ecf-4112-ac1f-b375d4ec2126

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FinalDS
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CircleIntegralInvSubEqZeroOfOutside

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Finset
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (N D A δ c : ℝ) (hNA : N ≤ A) (hD : A - δ ≤ D) (hc : 0 < c) (hcA : c ≤ A) (hδ : 0 ≤ δ)
    (h2 : 2 * δ ≤ A) : N ≤ Real.exp (2 * δ / c) * D := by
  have hA : 0 < A := lt_of_lt_of_le hc hcA
  have hAd : 0 < A - δ := by linarith
  have hA0 : A ≠ 0 := hA.ne'
  have hc0 : c ≠ 0 := hc.ne'
  have he : 1 + 2 * δ / c ≤ Real.exp (2 * δ / c) := by linarith [Real.add_one_le_exp (2 * δ / c)]
  have hdiv : 2 * δ / A ≤ 2 * δ / c := by
    have e : 2 * δ / c - 2 * δ / A = 2 * δ * (A - c) / (c * A) := by
      first
      | (field_simp; ring)
      | field_simp
    have : 0 ≤ 2 * δ * (A - c) / (c * A) :=
      div_nonneg (mul_nonneg (by linarith) (by linarith)) (mul_pos hc hA).le
    linarith
  have h3 : A ≤ (1 + 2 * δ / A) * (A - δ) := by
    have e : (1 + 2 * δ / A) * (A - δ) = A + δ - 2 * δ ^ 2 / A := by
      first
      | (field_simp; ring)
      | field_simp
    rw [e]
    have : 2 * δ ^ 2 / A ≤ δ := by
      rw [div_le_iff₀ hA]
      nlinarith [mul_nonneg hδ (sub_nonneg.mpr h2)]
    linarith
  have hexpos : 0 ≤ Real.exp (2 * δ / c) := (Real.exp_pos _).le
  calc N ≤ A := hNA
    _ ≤ (1 + 2 * δ / A) * (A - δ) := h3
    _ ≤ Real.exp (2 * δ / c) * (A - δ) := mul_le_mul_of_nonneg_right (by linarith) hAd.le
    _ ≤ Real.exp (2 * δ / c) * D := mul_le_mul_of_nonneg_left hD hexpos
end Formalism.HermitianLatticeCounting.P
