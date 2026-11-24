-- Prove2me | solution 1 for Formalism.L2.LamCM.geom_root_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:13:19.521037+00:00
-- url     : https://prove2.me/submissions/94f444b1-f9bd-43db-a7c7-942a2c69db1b

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CoeffMemOfLoc
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementA
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_OneLeAbsNormOfLeOne
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_AbsNormSpanGalois

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
namespace Formalism.L2.LamCM
theorem _root_.solution {ζ : ℂ} {N : ℕ} (hζ : IsPrimitiveRoot ζ N) {a b : ℕ} (ha : a < N) (hb : b < N) :
    ∑ j ∈ Finset.range N, (ζ ^ a * ζ⁻¹ ^ b) ^ j = if a = b then (N : ℂ) else 0 := by
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le a) ha
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hN.ne'
  split_ifs with hab
  · subst hab
    simp [mul_inv_cancel₀ (pow_ne_zero a hζ0)]
  · have hne : ζ ^ a * ζ⁻¹ ^ b ≠ 1 := by
      intro h
      apply hab
      apply hζ.pow_inj ha hb
      rw [inv_pow] at h
      exact (mul_inv_eq_one₀ (pow_ne_zero _ hζ0)).mp h
    rw [geom_sum_eq hne]
    have h1 : (ζ ^ a) ^ N = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    have h2 : (ζ⁻¹ ^ b) ^ N = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, inv_pow, hζ.pow_eq_one, inv_one, one_pow]
    rw [mul_pow, h1, h2, one_mul, sub_self, zero_div]
end Formalism.L2.LamCM
