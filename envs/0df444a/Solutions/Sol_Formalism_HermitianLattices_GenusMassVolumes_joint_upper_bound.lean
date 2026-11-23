-- Prove2me | solution 1 for Formalism.HermitianLattices.GenusMassVolumes.joint_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:27:41.251429+00:00
-- url     : https://prove2.me/submissions/42262d15-5ddc-4215-8169-3f03145dc3b0

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_RankMulPowThreeHalvesLeFourthPower
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_GaussianIntegralFormula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GenusMassVolumes
open Finset MeasureTheory
namespace Formalism.HermitianLattices.GenusMassVolumes
theorem _root_.solution : DegreeLeMulPowSignatureBound := by
  intro p q N d dτ c c₀ lamAbs hd hdτ hc hc₀ hl hN h1 h2
  set n := p * q with hn
  have hNR : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le one_pos hN)
  have hπ : 0 < Real.pi ^ n := pow_pos Real.pi_pos _
  have hcπ : 1 ≤ c * Real.pi ^ n := by
    rw [div_le_iff₀ hc] at h1; linarith
  have hf : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
  set A : ℝ := (c₀ / (2 * N * lamAbs)) ^ n with hA
  set B : ℝ := (2 * N * lamAbs / c₀) ^ n with hB
  have hApos : 0 < A := by positivity
  have hBpos : 0 < B := by positivity
  have hAB : A * B = 1 := by
    rw [hA, hB, ← mul_pow]
    have : c₀ / (2 * N * lamAbs) * (2 * N * lamAbs / c₀) = 1 := by field_simp
    rw [this, one_pow]
  have h3 : A / (n.factorial : ℝ) * (dτ / 4) ≤ dτ ^ 2 / d := by
    refine le_trans ?_ h2
    have : c * (Real.pi ^ n * A / (n.factorial : ℝ)) * (dτ / 4) =
        (c * Real.pi ^ n) * (A / (n.factorial : ℝ) * (dτ / 4)) := by ring
    rw [this]
    exact le_mul_of_one_le_left (by positivity) hcπ
  have h4 : d * A ≤ 4 * dτ * (n.factorial : ℝ) := by
    rw [le_div_iff₀ hd] at h3
    have h5 : A / (n.factorial : ℝ) * (dτ / 4) * d = (d * A) * (dτ / (4 * (n.factorial : ℝ))) := by
      field_simp
    rw [h5] at h3
    have h6 : 0 < dτ / (4 * (n.factorial : ℝ)) := by positivity
    have h7 : dτ ^ 2 = (4 * dτ * (n.factorial : ℝ)) * (dτ / (4 * (n.factorial : ℝ))) := by
      field_simp
    rw [h7] at h3
    exact le_of_mul_le_mul_right h3 h6
  have h8 : d ≤ 4 * dτ * (n.factorial : ℝ) * B := by
    calc d = d * A * B := by rw [mul_assoc, hAB, mul_one]
      _ ≤ 4 * dτ * (n.factorial : ℝ) * B := mul_le_mul_of_nonneg_right h4 hBpos.le
  have h9 : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
  calc d ≤ 4 * dτ * (n.factorial : ℝ) * B := h8
    _ ≤ 4 * dτ * (n : ℝ) ^ n * B := by gcongr
    _ = 4 * dτ * (2 / c₀ * (n : ℝ) * N * lamAbs) ^ n := by
        rw [hB, mul_assoc, ← mul_pow]
        congr 2
        field_simp
end Formalism.HermitianLattices.GenusMassVolumes
