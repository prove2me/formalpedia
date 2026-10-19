-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.quantitativeLowerBound_explicit_small
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.999068+00:00
-- url     : https://prove2.me/submissions/902dc088-ad78-420f-b703-3b774c99a980

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_triangleFree_lt_triangleRamseyNumber

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution (k : ℕ)
    (hk : 2 ≤ k) (hsmall : k < 342) :
    (((1 : ℝ) / (6 * Real.exp 38)) *
      (k : ℝ) ^ ((1 : ℝ) / 3) / Real.log (k : ℝ)) ^ k ≤
        (triangleRamseyNumber k : ℝ) := by
  have hlog : (1 / 2 : ℝ) ≤ Real.log (k : ℝ) := by
    calc
      (1 / 2 : ℝ) ≤ Real.log 2 := by
        nlinarith [Real.log_two_gt_d9]
      _ ≤ Real.log (k : ℝ) := by
        apply Real.log_le_log (by norm_num)
        exact_mod_cast hk
  have hroot : (k : ℝ) ^ ((1 : ℝ) / 3) ≤ (7 : ℝ) := by
    apply (pow_le_pow_iff_left₀
      (Real.rpow_nonneg (by positivity) _) (by positivity)
      (by norm_num : (3 : ℕ) ≠ 0)).mp
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
    exact_mod_cast (show k ≤ 343 by omega)
  have hexp : (39 : ℝ) ≤ Real.exp 38 := by
    nlinarith [Real.add_one_le_exp (38 : ℝ)]
  have hbase :
      ((1 : ℝ) / (6 * Real.exp 38)) *
        (k : ℝ) ^ ((1 : ℝ) / 3) / Real.log (k : ℝ) ≤ 1 := by
    apply (div_le_one (by linarith : 0 < Real.log (k : ℝ))).mpr
    calc
      ((1 : ℝ) / (6 * Real.exp 38)) *
          (k : ℝ) ^ ((1 : ℝ) / 3) ≤
          (1 / (6 * (39 : ℝ))) * 7 := by gcongr
      _ ≤ Real.log (k : ℝ) := by norm_num; linarith
  calc
    (((1 : ℝ) / (6 * Real.exp 38)) *
        (k : ℝ) ^ ((1 : ℝ) / 3) / Real.log (k : ℝ)) ^ k ≤
        (1 : ℝ) ^ k := by gcongr
    _ = 1 := one_pow _
    _ ≤ (triangleRamseyNumber k : ℝ) := by
      let C : SimpleGraph.TopEdgeLabeling (Fin 0) (Fin k) :=
        fun _ => ⟨0, by omega⟩
      exact_mod_cast triangleFree_lt_triangleRamseyNumber C
        (fun _ => SimpleGraph.cliqueFree_of_card_lt (by simp))
end ErdosProblems.MulticolourTriangleRamsey
