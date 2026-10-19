-- Prove2me | solution 1 for CohnElkies.upper_laplace_monomial_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:26.273981+00:00
-- url     : https://prove2.me/submissions/63d3b985-1dab-4b3a-a04a-43588b90ee3f

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {η : ℝ} (hη : 0 < η) (k : ℕ) :
    (∫ a : ℝ in Set.Ioi 0,
      a ^ k * Real.exp (-η * a)) =
        (k.factorial : ℝ) / η ^ (k + 1) := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by
    positivity
  calc
    (∫ a : ℝ in Set.Ioi 0,
      a ^ k * Real.exp (-η * a)) =
        ∫ a : ℝ in Set.Ioi 0,
          a ^ ((k : ℝ) + 1 - 1) *
            Real.exp (-(η * a)) := by
              apply setIntegral_congr_fun measurableSet_Ioi
              intro a ha
              change a ^ k * Real.exp (-η * a) =
                a ^ ((k : ℝ) + 1 - 1) *
                  Real.exp (-(η * a))
              rw [show (k : ℝ) + 1 - 1 = (k : ℝ) by ring,
                Real.rpow_natCast]
              congr 1
              ring_nf
    _ = (1 / η) ^ ((k : ℝ) + 1) *
          Real.Gamma ((k : ℝ) + 1) :=
      Real.integral_rpow_mul_exp_neg_mul_Ioi hk hη
    _ = (k.factorial : ℝ) / η ^ (k + 1) := by
      rw [show (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) by
        norm_num, Real.rpow_natCast]
      rw [show ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 by
        push_cast; ring, Real.Gamma_nat_eq_factorial]
      simp [inv_pow, div_eq_mul_inv, mul_comm]
end CohnElkies
