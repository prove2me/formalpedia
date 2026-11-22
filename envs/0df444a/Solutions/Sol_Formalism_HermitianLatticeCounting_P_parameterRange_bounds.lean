-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.parameterRange_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:30:19.168287+00:00
-- url     : https://prove2.me/submissions/d0017a3a-c8ac-461c-ab63-9ee4dd7be010

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExponentInequalityNondegenerateMid

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
theorem _root_.solution (C : ℝ) (hC : 1 ≤ C) (k m f : ℕ) (b g v NT Gam : ℝ)
    (h : Params C (16 * C ^ 32) k m f b g v NT Gam) :
    (4:ℝ) ≤ m ∧ (m:ℝ) ≤ f ∧ (f:ℝ) ≤ k ∧ 0.69 ≤ Real.log b ∧ 1 ≤ Real.log k ∧ 0 ≤ Real.log C ∧
    32 * Real.log C ≤ Real.log k ∧ 8 * (Real.log k + Real.log b) ≤ Real.log g ∧ 0 ≤ Real.log 2 ∧
    Real.log 2 ≤ Real.log b ∧ 16 * C ^ 32 * ((m:ℝ) ^ 5 * f * Real.log b) ≤ k ∧ 0 < g ∧ 0 < b ∧
    0 < v ∧ Real.log v ≤ Real.log b ∧ 0 < NT ∧ Real.log NT ≤ C * m * f * Real.log b ∧ 0 < Gam ∧
    0 ≤ Real.log Gam ∧ Real.log Gam ≤ C * (m:ℝ) ^ 5 * f * Real.log b := by
  unfold Params at h
  obtain ⟨hm, hmf, hfk, hb, hkbg, hK, hv1, hvb, hNT1, hNTb, hG1, hGe⟩ := h
  have hm' : (4 : ℝ) ≤ m := by exact_mod_cast hm
  have hmf' : (m : ℝ) ≤ f := by exact_mod_cast hmf
  have hfk' : (f : ℝ) ≤ k := by exact_mod_cast hfk
  have hb0 : 0 < b := by linarith
  have hl2b : Real.log 2 ≤ Real.log b := Real.log_le_log (by norm_num) hb
  have hlb : 0.69 ≤ Real.log b := by
    have := Real.log_two_gt_d9
    linarith
  have hC0 : 0 < C := by linarith
  have a1 : (1 : ℝ) ≤ C ^ 32 := one_le_pow₀ hC
  have a2 : (1 : ℝ) ≤ (m : ℝ) ^ 5 := one_le_pow₀ (by linarith)
  have a3 : (1 : ℝ) ≤ (m : ℝ) ^ 5 * f := one_le_mul_of_one_le_of_one_le a2 (by linarith)
  have a4 : 1 * 0.69 ≤ (m : ℝ) ^ 5 * f * Real.log b := mul_le_mul a3 hlb (by norm_num) (by linarith)
  have a5 : (m : ℝ) ^ 5 * f * Real.log b ≤ C ^ 32 * ((m : ℝ) ^ 5 * f * Real.log b) :=
    le_mul_of_one_le_left (by linarith) a1
  have hKk : 16 * C ^ 32 * ((m : ℝ) ^ 5 * f * Real.log b) ≤ k := by linarith
  have hk0 : (0 : ℝ) < k := by linarith
  have hlk : 1 ≤ Real.log k := by
    have he := Real.exp_one_lt_d9
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log k := Real.log_le_log (Real.exp_pos 1) (by linarith)
  have a6 : C ^ 32 * 1 ≤ C ^ 32 * (16 * ((m : ℝ) ^ 5 * f * Real.log b)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hC32k : C ^ 32 ≤ (k : ℝ) := by linarith
  have hlCk : 32 * Real.log C ≤ Real.log k := by
    have h1 := Real.log_le_log (by positivity) hC32k
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith
  have hkb0 : (0 : ℝ) < ((k : ℝ) * b) ^ 8 := by positivity
  have hg0 : 0 < g := lt_of_lt_of_le hkb0 hkbg
  have hlg : 8 * (Real.log k + Real.log b) ≤ Real.log g := by
    have h1 := Real.log_le_log hkb0 hkbg
    rw [Real.log_pow, Real.log_mul hk0.ne' hb0.ne'] at h1
    push_cast at h1
    linarith
  have hv0 : 0 < v := by linarith
  have hNT0 : 0 < NT := by linarith
  have hGam0 : 0 < Gam := by linarith
  have hlNT : Real.log NT ≤ C * m * f * Real.log b := by
    have h1 := Real.log_le_log hNT0 hNTb
    rwa [Real.log_rpow hb0] at h1
  have hlG : Real.log Gam ≤ C * (m : ℝ) ^ 5 * f * Real.log b := by
    have h1 := Real.log_le_log hGam0 hGe
    rwa [Real.log_exp] at h1
  exact ⟨hm', hmf', hfk', hlb, hlk, Real.log_nonneg hC, hlCk, hlg, Real.log_nonneg (by norm_num), hl2b,
    hKk, hg0, hb0, hv0, Real.log_le_log hv0 hvb, hNT0, hlNT, hGam0, Real.log_nonneg hG1, hlG⟩
end Formalism.HermitianLatticeCounting.P
