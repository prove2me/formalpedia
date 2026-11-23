-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.commonFactor_nonneg_and_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:07:32.977577+00:00
-- url     : https://prove2.me/submissions/1e9dc7a5-d9aa-4688-b27a-02f48db30c1f

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
theorem _root_.solution (C : ℝ) (hC : 1 ≤ C) (k m f s : ℕ) (b v Gam : ℝ) (Xi : ℕ → ℝ) (A : ℝ)
    (hb : 0 < b) (hv : 0 < v) (hGam : 0 < Gam) (hs1 : 1 ≤ s) (hsk : s ≤ k) (hf1 : 1 ≤ f)
    (hfk : f ≤ k) (hXi0 : 0 ≤ Xi s) (hA : ((k : ℝ) * v) ^ (k * f) * Xi s ≤ Real.exp A) :
    0 ≤ commonLatticeBound C k m f s b v Gam Xi ∧ commonLatticeBound C k m f s b v Gam Xi ≤
      Real.exp (A + (k:ℝ) * f * Real.log C +
        (C * (m:ℝ) ^ 2 * f * Real.log b) * (C * ((s : ℝ) + m) * (m : ℝ) ^ 2) +
        6 * (s:ℝ) * f * (Real.log C + 2 * Real.log k) + Real.log Gam) := by
  have hC0 : 0 < C := by linarith
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (hs1.trans hsk))
  have hs0 : (0 : ℝ) < s := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hs1)
  have hf0 : (0 : ℝ) < f := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hf1)
  have hCsf : 0 < C * s * f := mul_pos (mul_pos hC0 hs0) hf0
  have hX0 : 0 ≤ ((k : ℝ) * v) ^ (k * f) * Xi s := mul_nonneg (pow_nonneg (mul_pos hk0 hv).le _) hXi0
  have e1 : C ^ (k * f) = Real.exp ((k : ℝ) * f * Real.log C) := by
    rw [pow_eq_exp_mul_log C hC0, Nat.cast_mul]
  have e2 : bigH C m f b ^ (C * ((s : ℝ) + m) * (m : ℝ) ^ 2) =
      Real.exp ((C * (m : ℝ) ^ 2 * f * Real.log b) * (C * ((s : ℝ) + m) * (m : ℝ) ^ 2)) :=
    heightParameter_rpow C m f b _ hb
  have e3 : (C * s * f) ^ (6 * s * f) ≤ Real.exp (6 * (s : ℝ) * f * (Real.log C + 2 * Real.log k)) := by
    rw [pow_eq_exp_mul_log _ hCsf]
    apply Real.exp_le_exp.2
    have hl : Real.log (C * s * f) ≤ Real.log C + 2 * Real.log k := by
      rw [Real.log_mul (mul_pos hC0 hs0).ne' hf0.ne', Real.log_mul hC0.ne' hs0.ne']
      have h1 := Real.log_le_log hs0 (show (s : ℝ) ≤ k by exact_mod_cast hsk)
      have h2 := Real.log_le_log hf0 (show (f : ℝ) ≤ k by exact_mod_cast hfk)
      linarith
    have h6 : (0 : ℝ) ≤ ((6 * s * f : ℕ) : ℝ) := Nat.cast_nonneg _
    calc ((6 * s * f : ℕ) : ℝ) * Real.log (C * s * f)
        ≤ ((6 * s * f : ℕ) : ℝ) * (Real.log C + 2 * Real.log k) := mul_le_mul_of_nonneg_left hl h6
      _ = 6 * (s : ℝ) * f * (Real.log C + 2 * Real.log k) := by push_cast; ring
  unfold commonLatticeBound
  rw [e1, e2]
  refine ⟨?_, ?_⟩
  · exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hX0 (Real.exp_pos _).le) (Real.exp_pos _).le)
      (pow_nonneg hCsf.le _)) hGam.le
  · rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log hGam]
    refine mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA
      (Real.exp_pos _).le) (Real.exp_pos _).le) e3 (pow_nonneg hCsf.le _) (by positivity)) le_rfl hGam.le
      (by positivity)
end Formalism.HermitianLatticeCounting.P
