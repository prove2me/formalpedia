-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.minGainBaseLe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:58:42.066442+00:00
-- url     : https://prove2.me/submissions/192d44b5-a7ac-4d78-ae13-29307e031b5c

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_gainExponent_nonneg
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_gainExponent_le

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
theorem _root_.solution : XTilde := by
  intro k r C ν T' t g hk hC hν hT' ht hg hkt
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hk0 : (0:ℝ) < k := by linarith
  rcases le_or_gt ν T' with h | h
  · rw [min_eq_left h]; exact min_le_right _ _
  · rw [min_eq_right h.le]
    apply (min_le_left _ _).trans
    unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.xv
    have hge : 0 ≤ Formalism.HermitianLatticeCounting.LatticeSumBounds.expo k r := gainExponent_nonneg k r
    have hle : Formalism.HermitianLatticeCounting.LatticeSumBounds.expo k r ≤ 2 * r := gainExponent_le k r (by omega)
    have h1 : ((k:ℝ) ^ (2 * r))⁻¹ ≤ (C / k) ^ Formalism.HermitianLatticeCounting.LatticeSumBounds.expo k r := by
      calc ((k:ℝ) ^ (2 * r))⁻¹ = (1 / (k:ℝ)) ^ ((2 * r : ℕ) : ℝ) := by
            rw [Real.rpow_natCast, one_div, inv_pow]
        _ ≤ (1 / (k:ℝ)) ^ Formalism.HermitianLatticeCounting.LatticeSumBounds.expo k r :=
            Real.rpow_le_rpow_of_exponent_ge (one_div_pos.mpr hk0)
              (by rw [div_le_one hk0]; exact hk1) (by push_cast; exact hle)
        _ ≤ (C / k) ^ Formalism.HermitianLatticeCounting.LatticeSumBounds.expo k r :=
            Real.rpow_le_rpow (one_div_pos.mpr hk0).le
              (div_le_div_of_nonneg_right hC hk0.le) hge
    have h2 : 1 ≤ (k:ℝ) ^ (3 * r) * ((k:ℝ) ^ (2 * r))⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos hk0 _), one_mul]
      exact pow_le_pow_right₀ hk1 (by omega)
    calc (1:ℝ) ≤ (k:ℝ) ^ (3 * r) * ((k:ℝ) ^ (2 * r))⁻¹ := h2
      _ ≤ (g⁻¹ ^ (2 * r + 2) * T' * t) * (C / k) ^ Formalism.HermitianLatticeCounting.LatticeSumBounds.expo k r :=
          mul_le_mul hkt h1 (inv_nonneg.mpr (pow_nonneg hk0.le _)) (by positivity)
      _ = T' * t * g⁻¹ ^ (2 * r + 2) * (C / k) ^ Formalism.HermitianLatticeCounting.LatticeSumBounds.expo k r := by ring
end Formalism.HermitianLatticeCounting.P
