-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.minBoundSecondZero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:10:09.77293+00:00
-- url     : https://prove2.me/submissions/e9102bad-de84-4fdd-98fc-e558cf768655

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
theorem _root_.solution : MinIIZero := by
  intro k r CT G T T' g v t loss JHS dim hr hk hG hT hT' hg hv ht hloss hdim hCT hkt hVF
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0:ℝ) < k := by linarith
  have hg0 : 0 < g := by linarith
  have hg' : g ≠ 0 := hg0.ne'
  have hgp : 0 < g ^ (2 * r + 2) := pow_pos hg0 _
  have hkk : (k:ℝ) ≤ (k:ℝ) ^ (3 * r) := by
    calc (k:ℝ) = (k:ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (k:ℝ) ^ (3 * r) := pow_le_pow_right₀ hk1 (by omega)
  have h1 : (k:ℝ) ^ (3 * r) * g ^ (2 * r + 2) ≤ T' * t := by
    calc (k:ℝ) ^ (3 * r) * g ^ (2 * r + 2)
          ≤ (g⁻¹ ^ (2 * r + 2) * T' * t) * g ^ (2 * r + 2) :=
          mul_le_mul_of_nonneg_right hkt hgp.le
      _ = T' * t := by
          rw [show g⁻¹ ^ (2 * r + 2) * T' * t * g ^ (2 * r + 2) =
            (g ^ (2 * r + 2))⁻¹ * g ^ (2 * r + 2) * (T' * t) by ring, inv_mul_cancel₀ hgp.ne', one_mul]
  have hkey : (k:ℝ) * g ^ (2 * r + 2) ≤ T' * t :=
    (mul_le_mul_of_nonneg_right hkk hgp.le).trans h1
  have hCT' : T' ≤ CT * T := by rwa [div_le_iff₀ hT] at hCT
  have htT : 0 < t * T := mul_pos ht hT
  have hbase : (t * T)⁻¹ ≤ CT / (k * g ^ (2 * r + 2)) := by
    rw [le_div_iff₀ (mul_pos hk0 hgp)]
    calc (t * T)⁻¹ * (k * g ^ (2 * r + 2)) ≤ (t * T)⁻¹ * (CT * T * t) :=
          mul_le_mul_of_nonneg_left (by nlinarith) (inv_nonneg.mpr htT.le)
      _ = CT := by
          rw [show CT * T * t = (t * T) * CT by ring, ← mul_assoc, inv_mul_cancel₀ htT.ne',
            one_mul]
  have hTi : 0 ≤ T⁻¹ ^ k := by positivity
  calc Formalism.HermitianLatticeCounting.LatticeSumBounds.nv k r G T g v * JHS ^ 2 * T⁻¹ ^ k / dim
        = (Formalism.HermitianLatticeCounting.LatticeSumBounds.nv k r G T g v * JHS ^ 2 / dim) * T⁻¹ ^ k := by ring
    _ ≤ (loss * t⁻¹ ^ k) * T⁻¹ ^ k := mul_le_mul_of_nonneg_right hVF hTi
    _ = loss * ((t * T)⁻¹) ^ k := by ring
    _ ≤ loss * (CT / (k * g ^ (2 * r + 2))) ^ k :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hbase k) hloss
end Formalism.HermitianLatticeCounting.P
