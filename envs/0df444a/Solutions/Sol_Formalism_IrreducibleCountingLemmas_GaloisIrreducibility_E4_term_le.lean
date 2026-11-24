-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.E4.term_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:08:41.469543+00:00
-- url     : https://prove2.me/submissions/e7e42b1f-8098-4d78-81b3-0a42ffadc8ce

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateIVOfTypeSetWeight
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ProdPowFactorizationLe
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_FourMulSumLeProduct
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateThird

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
open Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.E4
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.E4
theorem _root_.solution (q δ b : ℕ) (hq : 2 ≤ q) (hδ : 2 ≤ δ)
    (h : δ * b ≤ δ * (q - 1) + (q ^ δ - 1) / (q - 1)) :
    (b : ℝ) * ((q : ℝ) ^ δ - 1)⁻¹ ≤ ((q : ℝ) ^ (δ - 1))⁻¹ + ((δ : ℝ))⁻¹ * ((q : ℝ) - 1)⁻¹ := by
  have hq1 : (1:ℝ) < q := by exact_mod_cast (by omega : 1 < q)
  have hB : (0:ℝ) < (q:ℝ) - 1 := by linarith
  have hD : (0:ℝ) < δ := by exact_mod_cast (by omega : 0 < δ)
  have hP1 : (1:ℝ) ≤ (q:ℝ) ^ (δ - 1) := one_le_pow₀ hq1.le
  have hP0 : (q:ℝ) ^ (δ - 1) ≠ 0 := by positivity
  have hpow : (q:ℝ) ^ δ = (q:ℝ) * (q:ℝ) ^ (δ - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hA : (0:ℝ) < (q:ℝ) ^ δ - 1 := by nlinarith
  have hcast : ((q ^ δ - 1 : ℕ) : ℝ) = (q:ℝ) ^ δ - 1 := by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Nat.cast_pow, Nat.cast_one]
  have hcast2 : ((q - 1 : ℕ) : ℝ) = (q:ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hR : (δ:ℝ) * b ≤ δ * ((q:ℝ) - 1) + ((q:ℝ) ^ δ - 1) / ((q:ℝ) - 1) := by
    have h' : ((δ * b : ℕ) : ℝ) ≤ ((δ * (q - 1) + (q ^ δ - 1) / (q - 1) : ℕ) : ℝ) :=
      Nat.cast_le.mpr h
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, hcast2] at h'
    have h'' : (((q ^ δ - 1) / (q - 1) : ℕ) : ℝ) ≤ ((q ^ δ - 1 : ℕ) : ℝ) / ((q - 1 : ℕ) : ℝ) :=
      Nat.cast_div_le
    rw [hcast, hcast2] at h''
    linarith
  have hstep : (b:ℝ) ≤ ((q:ℝ) - 1) + ((q:ℝ) ^ δ - 1) / ((q:ℝ) - 1) / δ := by
    rw [← sub_le_iff_le_add', le_div_iff₀ hD]
    nlinarith
  have e1 : ((q:ℝ) ^ (δ - 1))⁻¹ * ((q:ℝ) ^ δ - 1) = (q:ℝ) - ((q:ℝ) ^ (δ - 1))⁻¹ := by
    rw [hpow, mul_comm (q:ℝ) ((q:ℝ) ^ (δ - 1)), mul_sub, inv_mul_cancel_left₀ hP0, mul_one]
  have e2 : ((δ:ℝ))⁻¹ * ((q:ℝ) - 1)⁻¹ * ((q:ℝ) ^ δ - 1) =
      ((q:ℝ) ^ δ - 1) / ((q:ℝ) - 1) / δ := by
    ring
  have hPinv : ((q:ℝ) ^ (δ - 1))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hP1
  have key : (b:ℝ) ≤ (((q:ℝ) ^ (δ - 1))⁻¹ + ((δ:ℝ))⁻¹ * ((q:ℝ) - 1)⁻¹) * ((q:ℝ) ^ δ - 1) := by
    rw [add_mul, e1, e2]
    linarith
  calc (b:ℝ) * ((q:ℝ) ^ δ - 1)⁻¹
      ≤ ((((q:ℝ) ^ (δ - 1))⁻¹ + ((δ:ℝ))⁻¹ * ((q:ℝ) - 1)⁻¹) * ((q:ℝ) ^ δ - 1)) *
          ((q:ℝ) ^ δ - 1)⁻¹ :=
        mul_le_mul_of_nonneg_right key (inv_nonneg.mpr hA.le)
    _ = ((q:ℝ) ^ (δ - 1))⁻¹ + ((δ:ℝ))⁻¹ * ((q:ℝ) - 1)⁻¹ := mul_inv_cancel_right₀ hA.ne' _
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.E4
