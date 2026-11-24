-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.massRatioBound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:35.975835+00:00
-- url     : https://prove2.me/submissions/54e9e173-d956-4f1a-8728-d475c93902ec

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_one_le_zetaSeries
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_prod_zetaSeries_le
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_factorialPiWeight_pos
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_prod_massFactor
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_prod_factorialPiWeight_le

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
theorem _root_.solution : XiBound := by
  intro f k s v mass2 Lv hv hm2 hs hk hL
  have hv0 : 0 < v := by linarith
  have hA3 : ∀ j ∈ Finset.Ioc 2 s, 3 ≤ j := by intro j hj; rw [Finset.mem_Ioc] at hj; omega
  have hB3 : ∀ j ∈ Finset.Ioc (k - s) k, 3 ≤ j := by intro j hj; rw [Finset.mem_Ioc] at hj; omega
  have hzpos : ∀ j, 3 ≤ j → 0 < Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR j := fun j hj =>
    lt_of_lt_of_le one_pos (one_le_zetaSeries j (by omega))
  have hLpos : ∀ j, 3 ≤ j → 0 < Lv j := fun j hj =>
    lt_of_lt_of_le (inv_pos.mpr (pow_pos (hzpos j hj) f)) (hL j hj).1
  have hW : ∀ j, 0 < s5bA v j := factorialPiWeight_pos v hv0
  have hσ0 : 0 < Real.sqrt ((2 * v) ^ f) := Real.sqrt_pos.mpr (by positivity)
  have hσ2 : Real.sqrt ((2 * v) ^ f) ^ 2 = (2 * v) ^ f := Real.sq_sqrt (by positivity)
  have hPB0 : 0 < ∏ j ∈ Finset.Ioc (k - s) k, s5bA v j := Finset.prod_pos (fun j _ => hW j)
  have hLB0 : 0 < ∏ j ∈ Finset.Ioc (k - s) k, Lv j := Finset.prod_pos (fun j hj => hLpos j (hB3 j hj))
  have hR := prod_factorialPiWeight_le v hv k s hs hk
  have hratio : (∏ j ∈ Finset.Ioc 2 s, s5bA v j) /
      (∏ j ∈ Finset.Ioc (k - s) k, s5bA v j) ≤
      Real.pi ^ ((s - 2) * (k - s - 2)) * 17 *
        ((Real.exp 1 * Real.pi / (k * v)) ^ k * Real.sqrt (k / (2 * Real.pi))) := by
    rw [div_le_iff₀ hPB0]; exact hR
  have hLA : ∏ j ∈ Finset.Ioc 2 s, Lv j ≤ Real.exp 0.356 ^ f := by
    calc ∏ j ∈ Finset.Ioc 2 s, Lv j ≤ ∏ j ∈ Finset.Ioc 2 s, Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR j ^ f :=
          Finset.prod_le_prod (fun j hj => (hLpos j (hA3 j hj)).le) (fun j hj => (hL j (hA3 j hj)).2)
      _ = (∏ j ∈ Finset.Ioc 2 s, Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR j) ^ f := Finset.prod_pow _ _ _
      _ ≤ Real.exp 0.356 ^ f :=
          pow_le_pow_left₀ (Finset.prod_nonneg (fun j hj => (hzpos j (hA3 j hj)).le))
            (prod_zetaSeries_le _ hA3) f
  have hLB : (∏ j ∈ Finset.Ioc (k - s) k, Lv j)⁻¹ ≤ Real.exp 0.356 ^ f := by
    have h1 : ((∏ j ∈ Finset.Ioc (k - s) k, Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR j) ^ f)⁻¹ ≤ ∏ j ∈ Finset.Ioc (k - s) k, Lv j := by
      rw [← Finset.prod_pow, ← Finset.prod_inv_distrib]
      exact Finset.prod_le_prod (fun j hj => (inv_pos.mpr (pow_pos (hzpos j (hB3 j hj)) f)).le)
        (fun j hj => (hL j (hB3 j hj)).1)
    have h2 : 0 < (∏ j ∈ Finset.Ioc (k - s) k, Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR j) ^ f :=
      pow_pos (Finset.prod_pos (fun j hj => hzpos j (hB3 j hj))) f
    have h3 := inv_anti₀ (inv_pos.mpr h2) h1
    rw [inv_inv] at h3
    exact h3.trans (pow_le_pow_left₀ (Finset.prod_nonneg (fun j hj => (hzpos j (hB3 j hj)).le))
      (prod_zetaSeries_le _ hB3) f)
  have hexp : Real.exp 0.356 ^ f * Real.exp 0.356 ^ f ≤ Real.exp (0.72 * f) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by have := (Nat.cast_nonneg f : (0:ℝ) ≤ f); nlinarith)
  have key : ∀ (M PA PB LA LB σ : ℝ) (a : ℕ), 0 < PB → 0 < LB → 0 < σ →
      M * (PA ^ f * σ⁻¹ ^ a * LA) / (PB ^ f * σ⁻¹ ^ (a + 2) * LB) =
        M * (PA / PB) ^ f * σ ^ 2 * (LA * LB⁻¹) := by
    intro M PA PB LA LB σ a hPB hLB hσ
    have hP : PB ^ f * PB⁻¹ ^ f = 1 := by rw [← mul_pow, mul_inv_cancel₀ hPB.ne', one_pow]
    have hS : σ ^ 2 * σ⁻¹ ^ 2 = 1 := by rw [← mul_pow, mul_inv_cancel₀ hσ.ne', one_pow]
    have hL : LB * LB⁻¹ = 1 := mul_inv_cancel₀ hLB.ne'
    rw [div_eq_iff (by positivity)]
    linear_combination (-(M * PA ^ f * σ⁻¹ ^ a * LA) * (σ ^ 2 * σ⁻¹ ^ 2) * (LB * LB⁻¹)) * hP +
      (-(M * PA ^ f * σ⁻¹ ^ a * LA) * (LB * LB⁻¹)) * hS + (-(M * PA ^ f * σ⁻¹ ^ a * LA)) * hL
  rw [prod_massFactor, prod_massFactor, Nat.card_Ioc, Nat.card_Ioc, show k - (k - s) = s by omega]
  have hs' : (Real.sqrt ((2 * v) ^ f))⁻¹ ^ s = (Real.sqrt ((2 * v) ^ f))⁻¹ ^ ((s - 2) + 2) := by
    congr 1; omega
  rw [hs', key _ _ _ _ _ _ _ hPB0 hLB0 hσ0, hσ2]
  have hRf0 : 0 ≤ Real.pi ^ ((s - 2) * (k - s - 2)) * 17 *
      ((Real.exp 1 * Real.pi / (k * v)) ^ k * Real.sqrt (k / (2 * Real.pi))) := by positivity
  calc mass2 * ((∏ j ∈ Finset.Ioc 2 s, s5bA v j) /
          (∏ j ∈ Finset.Ioc (k - s) k, s5bA v j)) ^ f * (2 * v) ^ f *
          ((∏ j ∈ Finset.Ioc 2 s, Lv j) * (∏ j ∈ Finset.Ioc (k - s) k, Lv j)⁻¹)
        ≤ mass2 * (Real.pi ^ ((s - 2) * (k - s - 2)) * 17 *
            ((Real.exp 1 * Real.pi / (k * v)) ^ k * Real.sqrt (k / (2 * Real.pi)))) ^ f * (2 * v) ^ f *
          (Real.exp 0.356 ^ f * Real.exp 0.356 ^ f) :=
        mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (div_nonneg (Finset.prod_nonneg (fun j _ => (hW j).le)) hPB0.le) hratio f) hm2)
          (by positivity))
          (mul_le_mul hLA hLB (inv_nonneg.mpr hLB0.le) (by positivity))
          (mul_nonneg (Finset.prod_nonneg (fun j hj => (hLpos j (hA3 j hj)).le)) (inv_nonneg.mpr hLB0.le))
          (by positivity)
    _ ≤ mass2 * (Real.pi ^ ((s - 2) * (k - s - 2)) * 17 *
            ((Real.exp 1 * Real.pi / (k * v)) ^ k * Real.sqrt (k / (2 * Real.pi)))) ^ f * (2 * v) ^ f *
          Real.exp (0.72 * f) := mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = mass2 * (2 * v) ^ f * Real.exp (0.72 * f) * 17 ^ f * Real.sqrt (k / (2 * Real.pi)) ^ f *
          Real.pi ^ ((s - 2) * (k - s - 2) * f) * (Real.exp 1 * Real.pi / (k * v)) ^ (k * f) := by
        ring
end Formalism.HermitianLatticeCounting.P
