-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.final_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:05:36.037778+00:00
-- url     : https://prove2.me/submissions/077bd0bb-3576-4486-a5a1-6bbdfed3300f

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MinkowskiNumberDvdFactorial
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_fs_sizes
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_fs_arith
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_fs_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.S6.FinalSum := by
  intro C hC
  refine ⟨16 * C + C ^ 32, by positivity, ?_⟩
  intro k r f b d hb hf hd hyp
  have hr0 : (0:ℝ) ≤ r := Nat.cast_nonneg r
  have hmr : ((2 * r + 2 : ℕ) : ℝ) = 2 * r + 2 := by push_cast; ring
  generalize hm : ((2 * r + 2 : ℕ) : ℝ) = m at hyp hmr ⊢
  have hm2 : 2 ≤ m := by rw [hmr]; linarith
  have hL2 : 1 / 2 ≤ Real.log b := by
    have h1 : Real.log 2 ≤ Real.log b := Real.log_le_log (by norm_num) hb
    have h2 := Real.log_two_gt_d9
    linarith
  generalize Real.log b = L at hyp hL2 ⊢
  have hf1 : (1:ℝ) ≤ f := by exact_mod_cast hf
  have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
  have hm6 : (64:ℝ) ≤ m ^ 6 := by
    calc (64:ℝ) = 2 ^ 6 := by norm_num
      _ ≤ m ^ 6 := pow_le_pow_left₀ (by norm_num) hm2 6
  have hm62 : m * m ≤ m ^ 6 := by
    rw [← sq]; exact pow_le_pow_right₀ (by linarith) (by norm_num)
  have e32 : C ^ 32 = C ^ 16 * C ^ 16 := by ring
  rw [e32] at hyp
  obtain ⟨hk8, hkm, hkC, hmE, hE16, hCE⟩ := fs_sizes C m (m ^ 6) (C ^ 16) L k (Real.log k) hC hm6
    hm62 (by positivity) hL2 hk0 (Real.log_le_self hk0) hyp
  have hkpos : (0:ℝ) < k := by linarith
  have hl0 : 0 ≤ Real.log (k:ℝ) := Real.log_nonneg (by linarith)
  have hlogC : 16 * Real.log C ≤ Real.log (k:ℝ) := by
    have := Real.log_le_log (by positivity) hkC
    rw [Real.log_pow] at this
    simpa using this
  have hkN : 2 * r + 2 ≤ k := by
    rw [← hm] at hkm
    exact_mod_cast hkm
  have hx0 : 0 < C / (k:ℝ) := by positivity
  have hx1 : C / (k:ℝ) ≤ 1 := by
    rw [div_le_one hkpos]
    exact le_trans (le_self_pow₀ hC (by norm_num)) hkC
  obtain ⟨hS0, hS1⟩ := fs_sum (Real.exp (C * m ^ 6 * f * L)) (C / (k:ℝ)) (Real.exp_pos _).le hx0.le hx1 k r f
    (by omega)
  generalize (∑ j ∈ Finset.Icc 1 r, Real.exp (C * m ^ 6 * f * L) * (C / (k:ℝ)) ^ (j * (k - 1 - j) * f)) = S
    at hS0 hS1 ⊢
  have hxn : (C / (k:ℝ)) ^ ((k - 2) * f) =
      Real.exp ((((k:ℝ) - 2) * f) * (Real.log C - Real.log (k:ℝ))) := by
    have hncast : (((k - 2) * f : ℕ) : ℝ) = ((k:ℝ) - 2) * f := by
      push_cast [Nat.cast_sub (by omega : 2 ≤ k)]; ring
    rw [← hncast, ← Real.log_div (by positivity) hkpos.ne', Real.exp_nat_mul, Real.exp_log hx0]
  rw [hxn] at hS1
  have h2r : 2 * (r:ℝ) ^ 2 ≤ Real.exp (m ^ 6) := by
    have h1 : 2 * (r:ℝ) ^ 2 ≤ m * m := by rw [hmr]; nlinarith
    have h2 := Real.add_one_le_exp (m ^ 6)
    linarith
  have har := fs_arith C (m ^ 6) L k f (Real.log k) (Real.log C) hf1 hk8 hl0 hmE hE16 hCE hlogC
  have hmain : 2 * S ^ 2 ≤ Real.exp (-((k:ℝ) * f * Real.log k)) := by
    calc 2 * S ^ 2 ≤ 2 * (r * (Real.exp (C * m ^ 6 * f * L) *
            Real.exp ((((k:ℝ) - 2) * f) * (Real.log C - Real.log (k:ℝ))))) ^ 2 := by
          have := pow_le_pow_left₀ hS0 hS1 2
          linarith
      _ = (2 * (r:ℝ) ^ 2) * ((Real.exp (C * m ^ 6 * f * L) * Real.exp (C * m ^ 6 * f * L)) *
            (Real.exp ((((k:ℝ) - 2) * f) * (Real.log C - Real.log (k:ℝ))) *
              Real.exp ((((k:ℝ) - 2) * f) * (Real.log C - Real.log (k:ℝ))))) := by ring
      _ ≤ Real.exp (m ^ 6) * ((Real.exp (C * m ^ 6 * f * L) * Real.exp (C * m ^ 6 * f * L)) *
            (Real.exp ((((k:ℝ) - 2) * f) * (Real.log C - Real.log (k:ℝ))) *
              Real.exp ((((k:ℝ) - 2) * f) * (Real.log C - Real.log (k:ℝ))))) :=
          mul_le_mul_of_nonneg_right h2r (by positivity)
      _ = Real.exp (m ^ 6 + (C * m ^ 6 * f * L + C * m ^ 6 * f * L) +
            ((((k:ℝ) - 2) * f) * (Real.log C - Real.log (k:ℝ)) +
              (((k:ℝ) - 2) * f) * (Real.log C - Real.log (k:ℝ)))) := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
      _ ≤ Real.exp (-((k:ℝ) * f * Real.log k)) := Real.exp_le_exp.2 har
  calc 2 * d * S ^ 2 = d * (2 * S ^ 2) := by ring
    _ ≤ d * Real.exp (-((k:ℝ) * f * Real.log k)) := mul_le_mul_of_nonneg_left hmain hd
end Formalism.HermitianLatticeCounting.P
