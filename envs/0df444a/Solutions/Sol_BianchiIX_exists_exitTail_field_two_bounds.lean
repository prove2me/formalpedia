-- Prove2me | solution 1 for BianchiIX.exists_exitTail_field_two_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T18:59:36.725214+00:00
-- url     : https://prove2.me/submissions/02509967-44dc-4956-8d94-2149c407136b

import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_TerminalConnectionData
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Order.Compact

noncomputable section
open BianchiIX
open Set

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitTailGap_compact {R v : ℝ} (hR : 7 / 4 ≤ R) (hv : 0 ≤ v ∧ v ≤ 1) :
    1 ≤ exitTailGap R v ∧ exitTailGap R v ≤ R := by
  have hR0 : 0 ≤ R := by linarith only [hR]
  have hv2 : v ^ 2 ≤ 1 := by nlinarith only [hv.1, hv.2]
  refine ⟨?_, ?_⟩
  · exact (Real.le_sqrt (by norm_num) (by nlinarith only [hR, hv2])).mpr
      (by nlinarith only [hR, hv2])
  · exact (Real.sqrt_le_left hR0).mpr (by nlinarith only [sq_nonneg v])

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitTail_coupling_bound {u v w : ℝ} (hv : 0 ≤ v) :
    |coupling u v w| ≤ |u| * v + (|u| + |w|) ^ 2 := by
  have H : |v + w - u| ≤ v + |w| + |u| := by
    exact (abs_sub _ _).trans (add_le_add ((abs_add_le v w).trans_eq (by rw [abs_of_nonneg hv])) le_rfl)
  rw [coupling, abs_mul]
  have H' := mul_le_mul_of_nonneg_left H (abs_nonneg u)
  nlinarith only [H', mul_nonneg (abs_nonneg u) (abs_nonneg w), sq_nonneg |w|]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitTailSpeed_compact {R u v w : ℝ} (hR : 7 / 4 ≤ R)
    (hu : |u| ≤ 1 / 100) (hv : 0 ≤ v ∧ v ≤ 1) (hw : |w| ≤ 1 / 100) :
    1 / 2 ≤ exitTailSpeed R u v w := by
  have ht := (exitTailGap_compact hR hv).1
  have hc := exitTail_coupling_bound (u := u) (w := w) hv.1
  have huv : |u| * v ≤ 1 / 100 := by
    nlinarith only [mul_le_mul_of_nonneg_left hv.2 (abs_nonneg u), hu]
  have hb : (|u| + |w|) ^ 2 ≤ (1 / 50 : ℝ) ^ 2 := by
    nlinarith only [hu, hw, abs_nonneg u, abs_nonneg w]
  have H := neg_abs_le (coupling u v w)
  dsimp only [exitTailSpeed]
  linarith only [ht, hc, huv, hb, H]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.contDiffAt_exitTailField (n : WithTop ℕ∞) {v : ℝ} {Y : ExitTailState}
    (hv : v ^ 2 < (Y 0) ^ 2) (hR : Y 0 ≠ 0)
    (hd : exitTailSpeed (Y 0) (Y 1) v (Y 2) ≠ 0) :
    ContDiffAt ℝ n (fun q : ℝ × ExitTailState => exitTailField q.1 q.2) (v, Y) := by
  have hcoord (i : Fin 3) : ContDiffAt ℝ n (fun q : ℝ × ExitTailState => q.2 i) (v, Y) := by fun_prop
  have hgap : ContDiffAt ℝ n (fun q : ℝ × ExitTailState => exitTailGap (q.2 0) q.1) (v, Y) := by
    unfold exitTailGap
    exact (((hcoord 0).pow 2).sub (contDiffAt_fst.pow 2)).sqrt
      (ne_of_gt (sub_pos.mpr hv))
  have hc : ContDiffAt ℝ n (fun q : ℝ × ExitTailState => coupling (q.2 1) q.1 (q.2 2)) (v, Y) := by
    unfold coupling
    fun_prop
  have hs : ContDiffAt ℝ n (fun q : ℝ × ExitTailState => exitTailSpeed (q.2 0) (q.2 1) q.1 (q.2 2)) (v, Y) := hgap.add hc
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · change ContDiffAt ℝ n (fun q : ℝ × ExitTailState => exitTailRadial (q.2 0) (q.2 1) q.1 (q.2 2)) (v, Y)
    unfold exitTailRadial
    exact (((hc.neg.mul (hcoord 0)).sub
      ((hgap.mul (by fun_prop)).div (by fun_prop) hR)).div hs hd)
  · change ContDiffAt ℝ n (fun q : ℝ × ExitTailState => exitTailStrongRate (q.2 0) (q.2 1) q.1 (q.2 2) * q.2 1) (v, Y)
    unfold exitTailStrongRate
    apply ContDiffAt.mul _ (hcoord 1)
    have hn : ContDiffAt ℝ n (fun q : ℝ × ExitTailState =>
        2 * exitTailGap (q.2 0) q.1 - (q.2 0) ^ 2 + 2 * q.1 * q.2 2 - (q.2 2) ^ 2 + (q.2 1) ^ 2) (v, Y) := by fun_prop
    exact hn.div (contDiffAt_const.mul hs) (mul_ne_zero (by norm_num) hd)
  · change ContDiffAt ℝ n (fun q : ℝ × ExitTailState => exitTailWeakRate (q.2 0) (q.2 1) q.1 (q.2 2) * q.2 2) (v, Y)
    unfold exitTailWeakRate
    apply ContDiffAt.mul _ (hcoord 2)
    exact ((hgap.sub contDiffAt_const).sub hc).div hs hd

end
end

private theorem BianchiIX.contDiffAt_exitTail_stateDerivative (n : WithTop ℕ∞) {v : ℝ} {Y : ExitTailState}
    (hv : v ^ 2 < (Y 0) ^ 2) (hR : Y 0 ≠ 0)
    (hd : exitTailSpeed (Y 0) (Y 1) v (Y 2) ≠ 0) :
    ContDiffAt ℝ n (fun q : ℝ × ExitTailState => fderiv ℝ (exitTailField q.1) q.2) (v, Y) := by
  have hmap : ContDiffAt ℝ (n + 1)
      (fun q : (ℝ × ExitTailState) × ExitTailState => (q.1.1, q.2)) ((v, Y), Y) := by fun_prop
  have H := contDiffAt_exitTailField (n + 1) hv hR hd
  have HF := H.comp ((v, Y), Y) hmap
  exact HF.fderiv (f := fun q : ℝ × ExitTailState => exitTailField q.1) contDiffAt_snd le_rfl

private theorem BianchiIX.contDiffAt_exitTail_stateHessian (n : WithTop ℕ∞) {v : ℝ} {Y : ExitTailState}
    (hv : v ^ 2 < (Y 0) ^ 2) (hR : Y 0 ≠ 0)
    (hd : exitTailSpeed (Y 0) (Y 1) v (Y 2) ≠ 0) :
    ContDiffAt ℝ n (fun q : ℝ × ExitTailState => fderiv ℝ (fderiv ℝ (exitTailField q.1)) q.2) (v, Y) := by
  have hmap : ContDiffAt ℝ (n + 1)
      (fun q : (ℝ × ExitTailState) × ExitTailState => (q.1.1, q.2)) ((v, Y), Y) := by fun_prop
  have H := contDiffAt_exitTail_stateDerivative (n + 1) hv hR hd
  have HF := H.comp ((v, Y), Y) hmap
  exact HF.fderiv (f := fun q : ℝ × ExitTailState => fderiv ℝ (exitTailField q.1)) contDiffAt_snd le_rfl


/-- The full state Hessian is uniformly bounded on the signed tail box, including V = 0. -/
theorem solution :
    ∃ C ≥ (1 : ℝ), ∀ (v : ℝ) (Y : ExitTailState),
      (7 / 4 ≤ Y 0 ∧ Y 0 ≤ 17 / 4) → |Y 1| ≤ 1 / 100 →
      (0 ≤ v ∧ v ≤ 1) → |Y 2| ≤ 1 / 100 →
      ‖exitTailField v Y‖ ≤ C ∧ ‖fderiv ℝ (exitTailField v) Y‖ ≤ C ∧
        ‖fderiv ℝ (fderiv ℝ (exitTailField v)) Y‖ ≤ C := by
  let S : Set (ℝ × ExitTailState) := Icc (0, ![7 / 4, -(1 / 100), -(1 / 100)])
    (1, ![17 / 4, 1 / 100, 1 / 100])
  have hcompact : IsCompact S := isCompact_Icc
  let q := fun p : ℝ × ExitTailState => ‖exitTailField p.1 p.2‖ +
    ‖fderiv ℝ (exitTailField p.1) p.2‖ + ‖fderiv ℝ (fderiv ℝ (exitTailField p.1)) p.2‖
  have hq : ContinuousOn q S := by
    intro p hp
    have hR : 7 / 4 ≤ p.2 0 ∧ p.2 0 ≤ 17 / 4 := ⟨hp.1.2 0, hp.2.2 0⟩
    have hu : |p.2 1| ≤ 1 / 100 := abs_le.mpr ⟨hp.1.2 1, hp.2.2 1⟩
    have hv : 0 ≤ p.1 ∧ p.1 ≤ 1 := ⟨hp.1.1, hp.2.1⟩
    have hw : |p.2 2| ≤ 1 / 100 := abs_le.mpr ⟨hp.1.2 2, hp.2.2 2⟩
    have hvR : p.1 ^ 2 < (p.2 0) ^ 2 := by nlinarith only [hR.1, hv.1, hv.2]
    have hR0 : p.2 0 ≠ 0 := by linarith only [hR.1]
    have hd : exitTailSpeed (p.2 0) (p.2 1) p.1 (p.2 2) ≠ 0 := by
      have H := exitTailSpeed_compact hR.1 hu hv hw
      linarith only [H]
    have h0 : ContinuousAt (fun q : ℝ × ExitTailState => ‖exitTailField q.1 q.2‖) p :=
      (contDiffAt_exitTailField 0 hvR hR0 hd).continuousAt.norm
    have h1 : ContinuousAt (fun q : ℝ × ExitTailState => ‖fderiv ℝ (exitTailField q.1) q.2‖) p :=
      (contDiffAt_exitTail_stateDerivative 0 hvR hR0 hd).continuousAt.norm
    have HH := (contDiffAt_exitTail_stateHessian 0 hvR hR0 hd).continuousAt
    have h2 := ContinuousAt.norm (E := ExitTailState →L[ℝ] ExitTailState →L[ℝ] ExitTailState) HH
    exact ((h0.add h1).add h2).continuousWithinAt
  obtain ⟨B, hB⟩ := hcompact.exists_bound_of_continuousOn hq
  refine ⟨max B 1, le_max_right _ _, ?_⟩
  intro v Y hR hu hv hw
  have hYS : (v, Y) ∈ S := by
    constructor
    · refine ⟨hv.1, ?_⟩
      intro i
      fin_cases i
      · exact hR.1
      · exact (abs_le.mp hu).1
      · exact (abs_le.mp hw).1
    · refine ⟨hv.2, ?_⟩
      intro i
      fin_cases i
      · exact hR.2
      · exact (abs_le.mp hu).2
      · exact (abs_le.mp hw).2
  have H : q (v, Y) ≤ max B 1 := (le_abs_self _).trans ((hB (v, Y) hYS).trans (le_max_left _ _))
  dsimp only [q] at H
  exact ⟨by linarith [norm_nonneg (fderiv ℝ (exitTailField v) Y),
      norm_nonneg (fderiv ℝ (fderiv ℝ (exitTailField v)) Y)],
    by linarith [norm_nonneg (exitTailField v Y), norm_nonneg (fderiv ℝ (fderiv ℝ (exitTailField v)) Y)],
    by linarith [norm_nonneg (exitTailField v Y), norm_nonneg (fderiv ℝ (exitTailField v) Y)]⟩
