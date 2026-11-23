-- Prove2me | solution 1 for Comp.DiscountedCsgQ.dist_vOpt_le_of_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:04:29.959792+00:00
-- url     : https://prove2.me/submissions/9a61046d-0a0d-470a-ba43-88e7d857f6e4

import Definitions.Def_Comp_Shapley
import Definitions.Def_Csg_DiscountedValueIteration
import Definitions.Def_Comp_Iterate
import Theorems.Thm_Comp_DiscountedCsgQ_dist_cast_le
import Theorems.Thm_Comp_MatrixGameQ_toMatrixGame_A
import Theorems.Thm_Csg_DiscountedCSG_shapley_aposteriori_bound
import Theorems.Thm_Csg_DiscountedCSG_shapley_contracting
import Theorems.Thm_Csg_DiscountedCSG_vOpt_fixedPoint
attribute [local simp] Comp.MatrixGameQ.toMatrixGame_A



set_option autoImplicit true
open Comp
open Csg
open Comp.DiscountedCsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
namespace Comp.DiscountedCsgQ
theorem _root_.solution (G : DiscountedCsgQ S A1 A2) (h : G.WellFormed)
    {v w : S → ℚ} {d : ℚ} (hd0 : 0 ≤ d) (hd : ∀ s, |v s - w s| ≤ d)
    (hstep : ∀ s, (G.toDiscountedCSG h).shapley (fun s' => ((v s' : ℚ) : ℝ)) s
      = ((w s : ℚ) : ℝ)) :
    dist (fun s => ((w s : ℚ) : ℝ)) (G.toDiscountedCSG h).vOpt
      ≤ (G.toDiscountedCSG h).l * ((d : ℚ) : ℝ) / (1 - (G.toDiscountedCSG h).l) := by
  set D := G.toDiscountedCSG h with hD
  set V : S → ℝ := fun s => ((v s : ℚ) : ℝ) with hV
  set W : S → ℝ := fun s => ((w s : ℚ) : ℝ) with hW
  have hSV : D.shapley V = W := funext hstep
  have hap := D.shapley_aposteriori_bound V 0
  simp only [Function.iterate_zero_apply, zero_add, Function.iterate_one] at hap
  rw [hSV] at hap
  have hlcast : (D.lNN : ℝ) = D.l := rfl
  rw [hlcast] at hap
  have hc : dist W D.vOpt ≤ D.l * dist V D.vOpt := by
    have h1 := D.shapley_contracting V D.vOpt
    rwa [hSV, D.vOpt_fixedPoint] at h1
  have hVW : dist V W ≤ ((d : ℚ) : ℝ) := by
    rw [hV, hW]; exact dist_cast_le hd0 hd
  have hl0 : (0 : ℝ) ≤ D.l := D.l_nonneg
  have hl1 : (0 : ℝ) < 1 - D.l := by linarith [D.l_lt_one]
  rw [le_div_iff₀ hl1] at hap ⊢
  nlinarith [hap, hVW, hc, hl0, hl1, mul_le_mul_of_nonneg_left hap hl0,
    mul_le_mul_of_nonneg_left hVW hl0, mul_le_mul_of_nonneg_right hc hl1.le]
end Comp.DiscountedCsgQ
