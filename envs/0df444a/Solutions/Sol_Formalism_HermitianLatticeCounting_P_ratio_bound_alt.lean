-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.ratio_bound_alt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:43.820885+00:00
-- url     : https://prove2.me/submissions/7f8f36d7-2267-44d1-a756-39054d844d0c

import Definitions.Def_Formalism_FlagUnipotentLattices_LiftUnitaryFixesBase
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LiftingDecomposition

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
open CellDecomposition
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.S6.RatioBound := by
  intro C hC
  refine ⟨C ^ 2, ?_⟩
  intro k r f b g hb hf hlf hk hg
  have hexp : (2 * r + 2) ^ 2 = 4 * r ^ 2 + 8 * r + 4 := by ring
  have hm4 : 4 ≤ (2 * r + 2) ^ 2 := by omega
  have hC2 : C ≤ C ^ 2 := by nlinarith
  have hmk : (2 * r + 2) ^ 2 ≤ k := by nlinarith
  have hk4 : 4 ≤ k := by omega
  have hCk : C ≤ k := by nlinarith
  have hr4 : 4 * r ^ 2 ≤ k := by omega
  set n := k * f with hn
  have hn1 : 1 ≤ n := by rw [hn]; nlinarith
  have hb1 : (1 : ℝ) ≤ b := by linarith
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hCk' : (C : ℝ) ≤ k := by exact_mod_cast hCk
  have hg0 : 0 < g := lt_of_lt_of_le (by positivity) hg
  have h1 : (C : ℝ) ^ n ≤ (k : ℝ) ^ n := pow_le_pow_left₀ (by positivity) hCk' _
  have h2 : (b ^ (C * (2 * r + 2) ^ 2 * f)) ^ C ≤ b ^ n := by
    rw [← pow_mul]
    apply pow_le_pow_right₀ hb1
    calc C * (2 * r + 2) ^ 2 * f * C = (C ^ 2 * (2 * r + 2) ^ 2) * f := by ring
      _ ≤ k * f := Nat.mul_le_mul_right _ hk
  have hfexp : (f : ℝ) ≤ b ^ (2 * r ^ 2) := by
    have hfpos : (0 : ℝ) < f := by exact_mod_cast (by omega : 0 < f)
    have h0 : (f : ℝ) ≤ Real.exp ((r : ℝ) ^ 2) := (Real.log_le_iff_le_exp hfpos).1 hlf
    have e : Real.exp ((r : ℝ) ^ 2) = Real.exp 1 ^ (r ^ 2) := by
      rw [Real.exp_one_pow]; push_cast; rfl
    have he : Real.exp 1 ≤ b ^ 2 := by have := Real.exp_one_lt_d9; nlinarith
    calc (f : ℝ) ≤ Real.exp 1 ^ (r ^ 2) := by rw [← e]; exact h0
      _ ≤ (b ^ 2) ^ (r ^ 2) := pow_le_pow_left₀ (Real.exp_pos 1).le he _
      _ = b ^ (2 * r ^ 2) := by rw [← pow_mul]
  have h3 : ((C * k * f : ℕ) : ℝ) ^ (4 * f) ≤ (k : ℝ) ^ n * (k : ℝ) ^ n * b ^ (2 * n) := by
    push_cast
    rw [mul_pow, mul_pow]
    have a2 : (k : ℝ) ^ (4 * f) ≤ (k : ℝ) ^ n := pow_le_pow_right₀ hk1 (Nat.mul_le_mul_right _ hk4)
    have a1 : (C : ℝ) ^ (4 * f) ≤ (k : ℝ) ^ n := (pow_le_pow_left₀ (by positivity) hCk' _).trans a2
    have a3 : (f : ℝ) ^ (4 * f) ≤ b ^ (2 * n) :=
      calc (f : ℝ) ^ (4 * f) ≤ (b ^ (2 * r ^ 2)) ^ (4 * f) := pow_le_pow_left₀ (by positivity) hfexp _
        _ = b ^ (2 * r ^ 2 * (4 * f)) := (pow_mul _ _ _).symm
        _ ≤ b ^ (2 * n) := pow_le_pow_right₀ hb1 (by
            calc 2 * r ^ 2 * (4 * f) = 2 * ((4 * r ^ 2) * f) := by ring
              _ ≤ 2 * (k * f) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hr4))
    gcongr
  have h4 : (k : ℝ) ^ (8 * n) * b ^ (8 * n) ≤ g ^ n := by
    calc (k : ℝ) ^ (8 * n) * b ^ (8 * n) = (((k : ℝ) * b) ^ 8) ^ n := by rw [← pow_mul, mul_pow]
      _ ≤ g ^ n := pow_le_pow_left₀ (by positivity) hg _
  have h5 : 2 ≤ b ^ n := hb.trans (le_self_pow₀ hb1 (by omega))
  have hgn : 0 < g ^ n := by positivity
  have h6 : (k : ℝ) ^ (3 * n) * b ^ (3 * n) * 2 ≤ (k : ℝ) ^ (8 * n) * b ^ (8 * n) := by
    calc (k : ℝ) ^ (3 * n) * b ^ (3 * n) * 2 ≤ (k : ℝ) ^ (3 * n) * b ^ (3 * n) * b ^ n := by gcongr
      _ = (k : ℝ) ^ (3 * n) * b ^ (4 * n) := by rw [mul_assoc, ← pow_add]; congr 2; ring
      _ ≤ (k : ℝ) ^ (8 * n) * b ^ (8 * n) :=
          mul_le_mul (pow_le_pow_right₀ hk1 (by omega)) (pow_le_pow_right₀ hb1 (by omega))
            (by positivity) (by positivity)
  rw [div_pow, div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ hgn]
  calc (C : ℝ) ^ n * (b ^ (C * (2 * r + 2) ^ 2 * f)) ^ C * ((C * k * f : ℕ) : ℝ) ^ (4 * f)
      ≤ (k : ℝ) ^ n * b ^ n * ((k : ℝ) ^ n * (k : ℝ) ^ n * b ^ (2 * n)) := by gcongr
    _ = (k : ℝ) ^ (3 * n) * b ^ (3 * n) := by ring
    _ ≤ 1 / 2 * g ^ n := by linarith
end Formalism.HermitianLatticeCounting.P
