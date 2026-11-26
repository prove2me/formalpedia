-- Prove2me | solution 1 for FirstPassageLinearTransport.orbit_envelope_of_maximalBarrier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:25:57.54447+00:00
-- url     : https://prove2.me/submissions/9e27296c-2391-422e-b858-8e702a4c4aa8

import Mathlib.Algebra.Ring.GeomSum
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Definitions.Def_FirstPassageLinearTransport_Envelope
import Theorems.Thm_FirstPassageLinearTransport_logTwoThree_pos
import Theorems.Thm_FirstPassageLinearTransport_centralOrbitScale_pos
import Theorems.Thm_FirstPassageLinearTransport_normalizedCorrection_scaled_le_maximal
import Theorems.Thm_FirstPassageLinearTransport_three_rpow_eq_two_rpow_logTwoThree
import Theorems.Thm_FirstPassageLinearTransport_maximalBarrier_phase_half
import Theorems.Thm_FirstPassageLinearTransport_maximalBarrier_phase_two
import Theorems.Thm_FirstPassageLinearTransport_two_affineConstant_le_n_mul_central
import Theorems.Thm_FirstPassageLinearTransport_orbit_lower_of_fixed_barrier
import Theorems.Thm_FirstPassageLinearTransport_orbit_upper_of_fixed_barrier
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell



set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {n k M : ℕ} {t : ℝ}
    (ht : 0 < t) (hM : 4 ≤ M) (hstart : 2 ≤ t * M)
    (hkM : k ≤ M) (hnShell : n ∈ dyadicShell M)
    (hreg : MaximalParityRegular n M (maximalBarrierHeight t M)) :
    centralOrbitScale k * (n : ℝ) ^ (1 - t) ≤ (orbit k n : ℝ) ∧
      (orbit k n : ℝ) ≤ centralOrbitScale k * (n : ℝ) ^ (1 + t) := by
  have hnPos : 0 < n := by
    have hp : 0 < 2 ^ M := by positivity
    exact lt_of_lt_of_le hp (mem_dyadicShell.mp hnShell).1
  have hbounds := hreg k hkM
  have hSlo :
      (k : ℝ) / 2 - maximalBarrierHeight t M ≤ oddCount n k := by
    have := (abs_le.mp hbounds).1
    linarith
  have hShi :
      (oddCount n k : ℝ) ≤ (k : ℝ) / 2 + maximalBarrierHeight t M := by
    have := (abs_le.mp hbounds).2
    linarith
  have hphaseHalf := maximalBarrier_phase_half ht.le hnShell
  have hphase :
      (3 : ℝ) ^ maximalBarrierHeight t M ≤ (n : ℝ) ^ t := by
    have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hnPos
    exact hphaseHalf.trans
      (Real.rpow_le_rpow_of_exponent_le hnOne (by linarith))
  have hphaseTwo := maximalBarrier_phase_two ht hstart hnShell
  have hcorr := normalizedCorrection_scaled_le_maximal
    (n := n) (M := M) (k := k) (h := maximalBarrierHeight t M)
    hkM hreg
  have hscale := two_affineConstant_le_n_mul_central hM hkM hnShell
  have hcorrAbsorb :
      2 * ((2 + Real.sqrt 3) *
          (3 : ℝ) ^ maximalBarrierHeight t M *
          (3 : ℝ) ^ maximalBarrierHeight t M) ≤
        centralOrbitScale k * (n : ℝ) ^ (1 + t) := by
    have hphaseSq :
        (3 : ℝ) ^ maximalBarrierHeight t M *
            (3 : ℝ) ^ maximalBarrierHeight t M ≤ (n : ℝ) ^ t := by
      calc
        _ = (3 : ℝ) ^ (2 * maximalBarrierHeight t M) := by
          rw [← Real.rpow_add (by norm_num)]
          congr 1
          ring
        _ = (2 : ℝ) ^ (t * M) := by
          rw [three_rpow_eq_two_rpow_logTwoThree]
          congr 1
          unfold maximalBarrierHeight
          have hlog : logTwoThree ≠ 0 := ne_of_gt logTwoThree_pos
          field_simp [hlog]
        _ = ((2 : ℝ) ^ M) ^ t := by
          rw [mul_comm, Real.rpow_mul (by norm_num), Real.rpow_natCast]
        _ ≤ (n : ℝ) ^ t := by
          have hnLower : (2 : ℝ) ^ M ≤ n := by
            exact_mod_cast (mem_dyadicShell.mp hnShell).1
          exact Real.rpow_le_rpow (by positivity) hnLower ht.le
    have hmul :
        2 * (2 + Real.sqrt 3) *
            ((3 : ℝ) ^ maximalBarrierHeight t M *
              (3 : ℝ) ^ maximalBarrierHeight t M) ≤
          ((n : ℝ) * centralOrbitScale k) * (n : ℝ) ^ t :=
      mul_le_mul hscale hphaseSq (by positivity)
        (mul_nonneg (Nat.cast_nonneg n) (centralOrbitScale_pos k).le)
    rw [Real.rpow_add (by exact_mod_cast hnPos : (0 : ℝ) < n),
      Real.rpow_one]
    nlinarith
  exact ⟨orbit_lower_of_fixed_barrier hnPos hSlo hphase,
    orbit_upper_of_fixed_barrier hnPos hShi hphaseTwo hcorr hcorrAbsorb⟩
end FirstPassageLinearTransport
