-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.invFactorialLeStirling
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:51:31.880409+00:00
-- url     : https://prove2.me/submissions/e5300d96-ca6e-413a-a738-fac30cdb97e1

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
theorem _root_.solution : StirlingInv := by
  intro k hk
  have hk0 : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hst := Stirling.sqrt_pi_le_stirlingSeq (show k ≠ 0 by omega)
  unfold Stirling.stirlingSeq at hst
  have hπ := Real.pi_pos
  have ha0 : 0 < (Real.exp 1 / k) ^ k := by positivity
  have hka : ((k:ℝ) / Real.exp 1) ^ k = ((Real.exp 1 / k) ^ k)⁻¹ := by
    rw [← inv_pow, inv_div]
  rw [hka] at hst
  have hs0 : 0 < Real.sqrt (2 * k) * ((Real.exp 1 / k) ^ k)⁻¹ := by positivity
  rw [le_div_iff₀ hs0] at hst
  have hF : ((k - 1).factorial : ℝ) = (k.factorial : ℝ) / k := by
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul,
      mul_div_cancel_left₀ _ (by positivity : ((m + 1 : ℕ) : ℝ) ≠ 0)]
  rw [hF, one_div, inv_div, div_le_iff₀ (Nat.cast_pos.mpr (Nat.factorial_pos k))]
  have hsq : Real.sqrt (k / (2 * Real.pi)) * (Real.sqrt Real.pi * Real.sqrt (2 * k)) = k := by
    rw [← Real.sqrt_mul hπ.le, ← Real.sqrt_mul (by positivity)]
    rw [show (k:ℝ) / (2 * Real.pi) * (Real.pi * (2 * k)) = (k:ℝ) ^ 2 by
      rw [div_mul_eq_mul_div, div_eq_iff (by positivity)]; ring]
    exact Real.sqrt_sq hk0.le
  calc (k:ℝ) = Real.sqrt (k / (2 * Real.pi)) * (Real.sqrt Real.pi * Real.sqrt (2 * k)) := hsq.symm
    _ = ((Real.exp 1 / k) ^ k * ((Real.exp 1 / k) ^ k)⁻¹) *
          (Real.sqrt (k / (2 * Real.pi)) * (Real.sqrt Real.pi * Real.sqrt (2 * k))) := by
        rw [mul_inv_cancel₀ ha0.ne', one_mul]
    _ = (Real.exp 1 / k) ^ k * Real.sqrt (k / (2 * Real.pi)) *
          (Real.sqrt Real.pi * (Real.sqrt (2 * k) * ((Real.exp 1 / k) ^ k)⁻¹)) := by ring
    _ ≤ (Real.exp 1 / k) ^ k * Real.sqrt (k / (2 * Real.pi)) * (k.factorial : ℝ) :=
        mul_le_mul_of_nonneg_left hst (by positivity)
end Formalism.HermitianLatticeCounting.P
