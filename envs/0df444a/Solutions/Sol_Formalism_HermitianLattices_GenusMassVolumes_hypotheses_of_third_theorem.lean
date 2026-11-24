-- Prove2me | solution 1 for Formalism.HermitianLattices.GenusMassVolumes.hypotheses_of_third_theorem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:46:48.407773+00:00
-- url     : https://prove2.me/submissions/0488e7ce-3b50-4fd3-b6ac-71969d561a8c

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_RankMulPowThreeHalvesLeFourthPower
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_CardStabilizerVector
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_BlockDimensionIdentities
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DimensionMassJointBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GenusMassVolumes
open Finset
open Formalism.LogVandermondeBounds.StandardLattice
namespace Formalism.HermitianLattices.GenusMassVolumes
theorem _root_.solution : RankThresholdInequalityEventually := by
  intro ε C C₀ hε hC hC₀
  set a0 := 9 * C / 16 * Real.log 2 with ha0
  set a1 := 9 * C * C₀ / (16 * ε) with ha1
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have ha0n : 0 ≤ a0 := mul_nonneg (by positivity) hlog2
  have ha1n : 0 ≤ a1 := by positivity
  refine ⟨max 1 ((a0 + a1 + 1) ^ ε⁻¹), ?_⟩
  intro x hx f m k hm hme hmf hmk hkx
  dsimp only
  have hx1 : 1 ≤ x := le_trans (le_max_left _ _) hx
  have hx0 : 0 < x := by linarith
  have hy : a0 + a1 + 1 ≤ x ^ ε := by
    have h1 : (a0 + a1 + 1) ^ ε⁻¹ ≤ x := le_trans (le_max_right _ _) hx
    calc a0 + a1 + 1 = ((a0 + a1 + 1) ^ ε⁻¹) ^ ε :=
          (Real.rpow_inv_rpow (by positivity) hε.ne').symm
      _ ≤ x ^ ε := Real.rpow_le_rpow (by positivity) h1 hε.le
  obtain ⟨t, rfl⟩ : ∃ t, m = 2 * t + 2 := by
    obtain ⟨u, hu⟩ := hme
    exact ⟨u - 1, by omega⟩
  have eq1 : (2 * t + 2) / 2 = t + 1 := by omega
  have eq2 : k + (t + 1) - 1 = k + t := by omega
  have eq3 : k + (2 * t + 2) - 1 = k + 2 * t + 1 := by omega
  rw [eq1, eq2, eq3]
  have hR3 : (3 : ℝ) ≤ ((k + 2 * t + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 3 ≤ k + 2 * t + 1)
  refine ⟨?_, by omega, by omega, ?_⟩
  · have := Real.add_one_le_exp ((k + 2 * t + 1 : ℕ) : ℝ)
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num),
      show ((1 : ℝ) / 3)⁻¹ = 3 by norm_num]
    linarith
  · rw [Nat.cast_mul]
    have hRk : ((k + 2 * t + 1 : ℕ) : ℝ) ≤ 2 * x ^ C₀ := by
      have : ((k + 2 * t + 1 : ℕ) : ℝ) ≤ 2 * (k : ℝ) := by
        exact_mod_cast (by omega : k + 2 * t + 1 ≤ 2 * k)
      linarith
    have h2 : Real.log x ≤ x ^ ε / ε := Real.log_le_rpow_div hx0.le hε
    set R : ℝ := ((k + 2 * t + 1 : ℕ) : ℝ) with hR
    set Q : ℝ := ((t + 1 : ℕ) : ℝ) with hQ
    set P : ℝ := ((k + t : ℕ) : ℝ) with hP
    set y := x ^ ε with hydef
    have hQ1 : 1 ≤ Q := by rw [hQ]; exact_mod_cast (by omega : 1 ≤ t + 1)
    have hP0 : 0 ≤ P := by rw [hP]; positivity
    have hPR : P ≤ R := by rw [hP, hR]; exact_mod_cast (by omega : k + t ≤ k + 2 * t + 1)
    have hQf : 2 * Q ≤ f := by rw [hQ]; exact_mod_cast (by omega : 2 * (t + 1) ≤ f)
    have hy1 : 1 ≤ y := by linarith
    have hy0 : 0 ≤ y := by linarith
    have hlogR : Real.log R ≤ Real.log 2 + C₀ * (y / ε) := by
      have h1 : Real.log R ≤ Real.log (2 * x ^ C₀) := Real.log_le_log (by linarith) hRk
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hx0] at h1
      nlinarith [mul_le_mul_of_nonneg_left h2 hC₀]
    have hlog0 : 0 ≤ Real.log R := Real.log_nonneg (by linarith)
    have hkey : 9 * C / 16 * (Real.log 2 + C₀ * (y / ε)) ≤ y ^ 4 := by
      have e : 9 * C / 16 * (Real.log 2 + C₀ * (y / ε)) = a0 + a1 * y := by
        rw [ha0, ha1]
        field_simp
      rw [e]
      nlinarith [mul_le_mul_of_nonneg_left hy hy0, pow_le_pow_right₀ hy1 (by norm_num : 2 ≤ 4)]
    have hQ4 : Q ^ 4 ≤ (f : ℝ) ^ 4 / 16 := by
      have := pow_le_pow_left₀ (by linarith) hQf 4
      nlinarith
    have hPR3 : P ^ 3 * R ≤ R ^ 4 := by
      have := pow_le_pow_left₀ hP0 hPR 3
      nlinarith
    have hA := mul_le_mul hQ4 hPR3 (mul_nonneg (pow_nonneg hP0 3) (by linarith)) (by positivity)
    have hB := mul_le_mul_of_nonneg_left hA (mul_nonneg (by linarith : (0 : ℝ) ≤ 9 * C) hlog0)
    have hF : 0 ≤ (f : ℝ) ^ 4 * R ^ 4 := mul_nonneg (by positivity) (pow_nonneg (by linarith) 4)
    calc C * Q * (P * Q) ^ 3 * R * Real.log R / (1 / 3) ^ 2
        = 9 * C * Real.log R * (Q ^ 4 * (P ^ 3 * R)) := by ring
      _ ≤ 9 * C * Real.log R * ((f : ℝ) ^ 4 / 16 * R ^ 4) := hB
      _ = ((f : ℝ) ^ 4 * R ^ 4) * (9 * C / 16 * Real.log R) := by ring
      _ ≤ ((f : ℝ) ^ 4 * R ^ 4) * (9 * C / 16 * (Real.log 2 + C₀ * (y / ε))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlogR (by linarith)) hF
      _ ≤ ((f : ℝ) ^ 4 * R ^ 4) * y ^ 4 := mul_le_mul_of_nonneg_left hkey hF
      _ = (R * f * y) ^ 4 := by ring
end Formalism.HermitianLattices.GenusMassVolumes
