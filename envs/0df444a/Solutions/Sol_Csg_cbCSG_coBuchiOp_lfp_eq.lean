-- Prove2me | solution 1 for Csg.cbCSG_coBuchiOp_lfp_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:43:42.05083+00:00
-- url     : https://prove2.me/submissions/02ed0ab9-57f5-440f-a916-7dc9625ed0fd

import Definitions.Def_Csg_CoBuchiOp
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_SafetyCertificate
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_Csg_ConcurrentCoBuchiExample
import Theorems.Thm_Csg_cbInnerGfp_eq
import Theorems.Thm_Csg_cbGClosed_cbVStar
import Theorems.Thm_OrderHom_lfp_eq_of_certificate


set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution : (cbCSG.coBuchiOp cbU cbR_zero).lfp = cbVStar := by
  refine OrderHom.lfp_eq_of_certificate _ _ ?_ ?_
  · change (cbCSG.coBuchiInnerOp cbU cbR_zero cbVStar).gfp = cbVStar
    rw [cbInnerGfp_eq, cbGClosed_cbVStar]
  · intro b hb
    have hb' : cbGClosed b ≤ b := by
      rw [← cbInnerGfp_eq]; exact hb
    have h1 : (1 : ℝ) ≤ (b .t1 : ℝ) := hb' .t1
    have h3 : max ((b .t3 : ℝ)) (((b .t2 : ℝ) + (b .t4 : ℝ)) / 2) ≤ (b .t3 : ℝ) := hb' .t3
    have h3' : ((b .t2 : ℝ) + (b .t4 : ℝ)) / 2 ≤ (b .t3 : ℝ) := le_trans (le_max_right _ _) h3
    have h4nn : (0 : ℝ) ≤ (b .t4 : ℝ) := (b .t4).2.1
    have h2 : (1 + max ((b .t3 : ℝ)) (((b .t2 : ℝ) + (b .t4 : ℝ)) / 2)) / 2 ≤ (b .t2 : ℝ) := hb' .t2
    have h2' : (1 + (b .t3 : ℝ)) / 2 ≤ (b .t2 : ℝ) :=
      le_trans (by gcongr; exact le_max_left _ _) h2
    have ht3 : (1 : ℝ) / 3 ≤ (b .t3 : ℝ) := by linarith
    have ht2 : (2 : ℝ) / 3 ≤ (b .t2 : ℝ) := by linarith
    intro s
    cases s with
    | t1 => change cbVStarVal .t1 ≤ (b .t1 : ℝ); rw [cbVStarVal]; linarith
    | t2 => change cbVStarVal .t2 ≤ (b .t2 : ℝ); rw [cbVStarVal]; linarith
    | t3 => change cbVStarVal .t3 ≤ (b .t3 : ℝ); rw [cbVStarVal]; linarith
    | t4 => change cbVStarVal .t4 ≤ (b .t4 : ℝ); rw [cbVStarVal]; exact h4nn
    | t5 => change cbVStarVal .t5 ≤ (b .t5 : ℝ); rw [cbVStarVal]; exact (b .t5).2.1
end Csg
