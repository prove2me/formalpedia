-- Prove2me | solution 1 for FockSPR.exp_phi_le_factorial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:08:39.487618+00:00
-- url     : https://prove2.me/submissions/05360f6f-d035-47d1-9fa6-be3f6b82f42b

module
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_LaplaceFactorial
section
@[expose] public section
open Real MeasureTheory Set
noncomputable section
namespace FockSPR
private lemma phiFunc_rStar (n : ℕ) : phiFunc n (rStar n) =
    ((n : ℝ) + 1 / 2) * Real.log ((n : ℝ) + 1 / 2) - ((n : ℝ) + 1 / 2) := by
  unfold phiFunc rStar
  rw [Real.log_sqrt (by positivity : (0:ℝ) ≤ ↑n + 1 / 2),
      sq, Real.mul_self_sqrt (by positivity : (0:ℝ) ≤ ↑n + 1 / 2)]
  ring
private lemma phiFunc_rStar_le {n : ℕ} (hn : 1 ≤ n) :
    phiFunc n (rStar n) ≤
    (n : ℝ) * Real.log (n : ℝ) + (1 / 2) * Real.log (n : ℝ) - (n : ℝ) + 1 / 4 := by
  rw [phiFunc_rStar]
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have h1 : (0 : ℝ) < 1 + 1 / (2 * (n : ℝ)) := by positivity
  have h_expand : ((n : ℝ) + 1 / 2) * Real.log ((n : ℝ) + 1 / 2) =
      (n : ℝ) * Real.log (n : ℝ) + (1 / 2) * Real.log (n : ℝ) +
      ((n : ℝ) + 1 / 2) * Real.log (1 + 1 / (2 * (n : ℝ))) := by
    rw [show (n : ℝ) + 1 / 2 = (n : ℝ) * (1 + 1 / (2 * (n : ℝ))) from by field_simp,
        Real.log_mul (ne_of_gt hn_pos) (ne_of_gt h1)]
    ring_nf; rw [mul_inv_cancel₀ (ne_of_gt hn_pos)]; ring
  have h_log_bound : ((n : ℝ) + 1 / 2) * Real.log (1 + 1 / (2 * (n : ℝ))) ≤ 3 / 4 := by
    calc ((n : ℝ) + 1 / 2) * Real.log (1 + 1 / (2 * (n : ℝ)))
        ≤ ((n : ℝ) + 1 / 2) * (1 / (2 * (n : ℝ))) :=
          mul_le_mul_of_nonneg_left
            (by linarith only [h1, Real.log_le_sub_one_of_pos h1]) (by linarith only [hn_pos])
      _ = 1 / 2 + 1 / (4 * (n : ℝ)) := by field_simp; ring
      _ ≤ 3 / 4 := by
          linarith [div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1)
            (by norm_num : (0:ℝ) < 4)
            (show (4:ℝ) ≤ 4 * (n:ℝ) from by
              nlinarith [show (1:ℝ) ≤ (n:ℝ) from by exact_mod_cast hn])]
  linarith only [h_expand, h_log_bound]
private lemma stirling_log_bound {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) * Real.log (n : ℝ) + (1 / 2) * Real.log (n : ℝ) - (n : ℝ) ≤
    Real.log (n.factorial : ℝ) - Real.log 2 := by
  have h_stirling := @Stirling.le_log_factorial_stirling n (by omega)
  have h_pi : Real.log 2 ≤ (1 / 2) * Real.log (2 * π) := by
    have : Real.log 4 ≤ Real.log (2 * π) :=
      Real.log_le_log (by norm_num) (by linarith only [Real.two_le_pi])
    linarith only [this,
        show Real.log 4 = 2 * Real.log 2 from
          by
          rw [show (4 : ℝ) = 2 ^ 2 from by norm_num, Real.log_pow]
          simp only [Nat.cast_ofNat]]
  linarith only [h_stirling, h_pi]
end FockSPR
end
end
end

set_option autoImplicit true
@[expose] public section
public section
open Real MeasureTheory Set
noncomputable section
open FockSPR
namespace FockSPR
theorem _root_.solution {n : ℕ} (hn : 1 ≤ n) :
    Real.exp (phiFunc n (rStar n)) ≤
    Real.exp (1 / 4) * (Nat.factorial n : ℝ) / 2 := by
  have h3 : phiFunc n (rStar n) ≤
      Real.log (n.factorial : ℝ) - Real.log 2 + 1 / 4 := by
    linarith only [phiFunc_rStar_le hn, stirling_log_bound hn]
  have h_fact_pos : (0 : ℝ) < (n.factorial : ℝ) :=
    Nat.cast_pos.mpr n.factorial_pos
  calc Real.exp (phiFunc n (rStar n))
      ≤ Real.exp (Real.log (n.factorial : ℝ) - Real.log 2 + 1 / 4) :=
        Real.exp_le_exp.mpr h3
    _ = Real.exp (1 / 4 + Real.log ((n.factorial : ℝ) / 2)) := by
        congr 1
        rw [Real.log_div (ne_of_gt h_fact_pos) (by norm_num)]
        ring
    _ = Real.exp (1 / 4) * ((n.factorial : ℝ) / 2) := by
        rw [Real.exp_add, Real.exp_log (by positivity)]
    _ = Real.exp (1 / 4) * (n.factorial : ℝ) / 2 := by ring
end FockSPR
