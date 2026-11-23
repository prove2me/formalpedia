-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.massRatio_bound_of_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:10:09.423694+00:00
-- url     : https://prove2.me/submissions/f5b83af4-4afb-4027-8d57-826e1e8aca39

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExponentInequalityNondegenerateMid
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_pow_eq_exp_mul_log
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_heightParameter_rpow

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
theorem _root_.solution (C : ℝ) (hC : 1 ≤ C) (k m f s : ℕ) (b v NT : ℝ) (Xi : ℕ → ℝ) (hb : 0 < b)
    (hv : 0 < v) (hNT : 0 < NT) (hk : 1 ≤ k) (hlv : Real.log v ≤ Real.log b)
    (hlNT : Real.log NT ≤ C * m * f * Real.log b)
    (hXi : XiHyp C k m f b v NT Xi) (hs : s + 1 = k ∨ s = k) :
    0 ≤ Xi s ∧ ((k : ℝ) * v) ^ (k * f) * Xi s ≤
      Real.exp ((k:ℝ) * f * (Real.log k + Real.log b) + ((k:ℝ) * f * (Real.log C + Real.log k) +
        ((C * (m:ℝ) ^ 2 * f * Real.log b) * (C * m) + C * m * f * Real.log b) * (C * k))) := by
  unfold XiHyp at hXi
  obtain ⟨h0, h1⟩ := hXi.2 s hs
  refine ⟨h0, ?_⟩
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hC0 : 0 < C := by linarith
  have hH : 0 < bigH C m f b ^ (C * m) := by
    rw [heightParameter_rpow C m f b _ hb]
    exact Real.exp_pos _
  have hkv : ((k : ℝ) * v) ^ (k * f) ≤ Real.exp ((k : ℝ) * f * (Real.log k + Real.log b)) := by
    rw [pow_eq_exp_mul_log _ (mul_pos hk0 hv), Real.log_mul hk0.ne' hv.ne', Nat.cast_mul]
    apply Real.exp_le_exp.2
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hCk : (C * k) ^ (k * f) = Real.exp ((k : ℝ) * f * (Real.log C + Real.log k)) := by
    rw [pow_eq_exp_mul_log _ (mul_pos hC0 hk0), Real.log_mul hC0.ne' hk0.ne', Nat.cast_mul]
  have hB : (bigH C m f b ^ (C * m) * NT) ^ (C * k) ≤
      Real.exp (((C * (m : ℝ) ^ 2 * f * Real.log b) * (C * m) + C * m * f * Real.log b) * (C * k)) := by
    rw [Real.rpow_def_of_pos (mul_pos hH hNT), Real.log_mul hH.ne' hNT.ne', heightParameter_rpow C m f b _ hb,
      Real.log_exp]
    apply Real.exp_le_exp.2
    exact mul_le_mul_of_nonneg_right (by linarith) (mul_pos hC0 hk0).le
  calc ((k : ℝ) * v) ^ (k * f) * Xi s ≤ Real.exp ((k : ℝ) * f * (Real.log k + Real.log b)) *
        ((C * k) ^ (k * f) * (bigH C m f b ^ (C * m) * NT) ^ (C * k)) :=
        mul_le_mul hkv h1 h0 (Real.exp_pos _).le
    _ ≤ Real.exp ((k : ℝ) * f * (Real.log k + Real.log b)) *
        (Real.exp ((k : ℝ) * f * (Real.log C + Real.log k)) *
          Real.exp (((C * (m : ℝ) ^ 2 * f * Real.log b) * (C * m) + C * m * f * Real.log b) * (C * k))) := by
        rw [hCk]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hB (Real.exp_pos _).le) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]
end Formalism.HermitianLatticeCounting.P
