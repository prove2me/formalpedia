-- Prove2me | solution 1 for Formalism.GM.GaussNormRoots.vmin_step
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:21:07.656274+00:00
-- url     : https://prove2.me/submissions/6a0eff0c-b278-4ca6-8066-41d0d6b50624

import Definitions.Def_Formalism_MahlerMeasure_LieRoots
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieRoots

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open Finset Polynomial
open Formalism.GM.GaussNormRoots
namespace Formalism.GM.GaussNormRoots
theorem _root_.solution (p : ℕ) (hp1 : (1 : ℝ) < p) (h : ℕ) (E : ℝ) (hE : 0 ≤ E) (u : ℝ) (_hu : 0 ≤ u)
    [Decidable (u ≤ (p : ℝ) ^ (-(h : ℤ)))] :
    -Real.logb p (max u ((p : ℝ) ^ (-((h : ℝ) + E)))) ≤
      -Real.logb p (max u ((p : ℝ) ^ (-(h : ℤ)))) + E * (if u ≤ (p : ℝ) ^ (-(h : ℤ)) then 1 else 0) := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hB : (0 : ℝ) < (p : ℝ) ^ (-((h : ℝ) + E)) := Real.rpow_pos_of_pos hp0 _
  have hAeq : (p : ℝ) ^ (-(h : ℤ)) = (p : ℝ) ^ (-(h : ℝ)) := by
    rw [← Real.rpow_intCast]
    norm_num
  have hBA : (p : ℝ) ^ (-((h : ℝ) + E)) ≤ (p : ℝ) ^ (-(h : ℤ)) := by
    rw [hAeq]
    exact Real.rpow_le_rpow_of_exponent_le hp1.le (by linarith)
  split_ifs with hu
  · rw [max_eq_right hu, mul_one]
    have h1 : Real.logb p ((p : ℝ) ^ (-((h : ℝ) + E))) ≤
        Real.logb p (max u ((p : ℝ) ^ (-((h : ℝ) + E)))) :=
      Real.logb_le_logb_of_le hp1 hB (le_max_right _ _)
    have h2 : Real.logb p ((p : ℝ) ^ (-((h : ℝ) + E))) = -((h : ℝ) + E) :=
      Real.logb_rpow hp0 hp1.ne'
    have h3 : Real.logb p ((p : ℝ) ^ (-(h : ℤ))) = -(h : ℝ) := by
      rw [hAeq]
      exact Real.logb_rpow hp0 hp1.ne'
    linarith
  · push_neg at hu
    rw [max_eq_left (le_trans hBA hu.le), max_eq_left hu.le]
    simp
end Formalism.GM.GaussNormRoots
