-- Prove2me | solution 1 for BraidsLinksMCG.puncturedPlane_standardGen_new_loop_mem_right_factor_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-24T13:22:25.252078+00:00
-- url     : https://prove2.me/submissions/00f03d30-b1d4-4ecf-82a5-b0d91e670fa3

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_BraidsLinksMCG_StandardLoops

open BraidsLinksMCG

/-
The named loop around the newly added puncture stays in the right factor of the
corrected v3 matched cover. This is the coordinate part of the new-factor
generator certificate; it does not assert that the loop freely generates the
factor.
-/

private theorem path_re_gt_trans {X : Type*} [TopologicalSpace X] {x y z : X}
    (f : X → ℝ) (R : ℝ)
    (p : Path x y) (q : Path y z)
    (hp : ∀ t, R < f (p t)) (hq : ∀ t, R < f (q t)) :
    ∀ t, R < f ((p.trans q) t) := by
  intro t
  rw [Path.trans_apply]
  split_ifs
  · exact hp _
  · exact hq _

private lemma new_approachFun_re_gt_factorThreshold (n : ℕ) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ((n : ℝ) + 1) - 3 / 4 <
      (approachFun (n + 1) (Fin.last n) t).re := by
  simp [approachFun]
  norm_num [Fin.val_last]
  nlinarith [ht1]

private lemma new_circleFun_re_gt_factorThreshold (n : ℕ) (t : ℝ) :
    ((n : ℝ) + 1) - 3 / 4 <
      (circleFun (n + 1) (Fin.last n) t).re := by
  have hc : -1 ≤ Real.cos (2 * Real.pi * t) := by
    exact Real.neg_one_le_cos _
  have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  have hre :
      (circleFun (n + 1) (Fin.last n) t).re =
        ((n : ℝ) + 1) + (1 / 2) * Real.cos (2 * Real.pi * t) := by
    rw [circleFun, Complex.exp_ofReal_mul_I, hhalf]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero, mul_one,
      sub_zero, add_zero, Complex.natCast_re, Complex.one_re]
    norm_num [Fin.val_last]
  rw [hre]
  linarith

private lemma standardLoop_new_re_gt_factorThreshold (n : ℕ) (t : unitInterval) :
    ((n : ℝ) + 1) - 3 / 4 <
      (standardLoop (n + 1) (Fin.last n) t).1.re := by
  have happ : ∀ u : unitInterval,
      ((n : ℝ) + 1) - 3 / 4 <
        (approachPath (n + 1) (Fin.last n) u).1.re := by
    intro u
    simpa [approachPath] using
      new_approachFun_re_gt_factorThreshold n (u : ℝ) u.2.1 u.2.2
  have hcir : ∀ u : unitInterval,
      ((n : ℝ) + 1) - 3 / 4 <
        (circlePath (n + 1) (Fin.last n) u).1.re := by
    intro u
    simpa [circlePath] using
      new_circleFun_re_gt_factorThreshold n (u : ℝ)
  have hback : ∀ u : unitInterval,
      ((n : ℝ) + 1) - 3 / 4 <
        ((approachPath (n + 1) (Fin.last n)).symm u).1.re := by
    intro u
    rw [Path.symm_apply]
    exact happ _
  have hinner := path_re_gt_trans
    (fun z : PuncturedPlane (n + 1) => z.1.re)
    ((n : ℝ) + 1 - 3 / 4)
    (circlePath (n + 1) (Fin.last n))
    ((approachPath (n + 1) (Fin.last n)).symm)
    hcir hback
  have hloop := path_re_gt_trans
    (fun z : PuncturedPlane (n + 1) => z.1.re)
    ((n : ℝ) + 1 - 3 / 4)
    (approachPath (n + 1) (Fin.last n))
    ((circlePath (n + 1) (Fin.last n)).trans
      (approachPath (n + 1) (Fin.last n)).symm)
    happ hinner
  simpa [standardLoop] using hloop t

/-- The actual new standard loop lies pointwise in the right member of the
corrected v3 matched cover. -/
theorem solution
    (n : ℕ) (t : unitInterval) :
    (standardLoop (n + 1) (Fin.last n) t) ∈
      {z : PuncturedPlane (n + 1) |
        ((n : ℝ) + 1) - 3 / 4 < z.1.re} := by
  exact standardLoop_new_re_gt_factorThreshold n t
