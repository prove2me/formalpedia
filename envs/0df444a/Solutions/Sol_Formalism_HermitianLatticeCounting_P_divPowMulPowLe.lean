-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.divPowMulPowLe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:05:23.411526+00:00
-- url     : https://prove2.me/submissions/1913e9d6-f1f6-4ef2-ab99-02af388e0eac

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
theorem _root_.solution : DivPowMulPowLe := by
  intro k de₀ j₀ t₁ t₂ De NT cf hde hj ht1 ht2 hNT hcf hDe
  have hde0 : 0 < de₀ := by linarith
  have hP1 : 1 ≤ j₀ * t₁ * t₂ :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hj ht1) ht2
  have hP0 : 0 < j₀ * t₁ * t₂ := by linarith
  have hPDe : j₀ * t₁ * t₂ ≤ De := by nlinarith
  have hDe0 : 0 < De := by linarith
  rw [Real.rpow_add hP0, Real.rpow_natCast]
  have h1 : (de₀ / NT) ^ k * (j₀ * t₁ * t₂) ^ k ≤ (De / NT) ^ k := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (by nlinarith) hNT.le
  have h2 : (j₀ * t₁ * t₂) ^ cf ≤ De ^ cf := Real.rpow_le_rpow hP0.le hPDe hcf
  calc _ = ((de₀ / NT) ^ k * (j₀ * t₁ * t₂) ^ k) * (j₀ * t₁ * t₂) ^ cf := by ring
    _ ≤ (De / NT) ^ k * De ^ cf := mul_le_mul h1 h2 (by positivity) (by positivity)
end Formalism.HermitianLatticeCounting.P
