-- Prove2me | solution 1 for Comp.DiscountedCsgQ.two_dist_vOpt_lt_of_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:07:37.597444+00:00
-- url     : https://prove2.me/submissions/1ddf7da7-a936-4d51-9af4-03141d6efedc

import Definitions.Def_Comp_Shapley
import Definitions.Def_Csg_DiscountedValueIteration
import Definitions.Def_Comp_Iterate
import Theorems.Thm_Comp_DiscountedCsgQ_dist_vOpt_le_of_step

set_option autoImplicit true
open Comp
open Csg
open Comp.DiscountedCsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
namespace Comp.DiscountedCsgQ
theorem _root_.solution (G : DiscountedCsgQ S A1 A2) (h : G.WellFormed)
    {v w : S → ℚ} {d eps : ℚ} (hd0 : 0 ≤ d) (hd : ∀ s, |v s - w s| ≤ d)
    (hstep : ∀ s, (G.toDiscountedCSG h).shapley (fun s' => ((v s' : ℚ) : ℝ)) s
      = ((w s : ℚ) : ℝ))
    (hstop : 2 * G.l * d < eps * (1 - G.l)) :
    2 * dist (fun s => ((w s : ℚ) : ℝ)) (G.toDiscountedCSG h).vOpt < ((eps : ℚ) : ℝ) := by
  have hDl : (G.toDiscountedCSG h).l = ((G.l : ℚ) : ℝ) := rfl
  have hb := dist_vOpt_le_of_step G h hd0 hd hstep
  rw [hDl] at hb
  have hl0 : (0 : ℝ) ≤ ((G.l : ℚ) : ℝ) := by exact_mod_cast h.2.1
  have hl1 : ((G.l : ℚ) : ℝ) < 1 := by exact_mod_cast h.2.2
  have hstopR : 2 * ((G.l : ℚ) : ℝ) * ((d : ℚ) : ℝ)
      < ((eps : ℚ) : ℝ) * (1 - ((G.l : ℚ) : ℝ)) := by exact_mod_cast hstop
  have hpos : (0 : ℝ) < 1 - ((G.l : ℚ) : ℝ) := by linarith
  rw [le_div_iff₀ hpos] at hb
  have h2 : (2 * dist (fun s => ((w s : ℚ) : ℝ)) (G.toDiscountedCSG h).vOpt)
      * (1 - ((G.l : ℚ) : ℝ)) < ((eps : ℚ) : ℝ) * (1 - ((G.l : ℚ) : ℝ)) := by
    nlinarith [hb, hstopR]
  exact lt_of_mul_lt_mul_right h2 (by linarith : (0 : ℝ) ≤ 1 - ((G.l : ℚ) : ℝ))
end Comp.DiscountedCsgQ
