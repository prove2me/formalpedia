-- Prove2me | solution 1 for BianchiIX.exitTailField_jacobian_norm_bound
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T19:31:09.615752+00:00
-- url     : https://prove2.me/submissions/c0103916-b544-442e-bde0-aeb946397f42

import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_TerminalConnectionData
import Definitions.Def_BianchiIX_TerminalConeData
import Theorems.Thm_BianchiIX_exitTail_radial_gradient_bounds
import Theorems.Thm_BianchiIX_exitTail_rate_gradient_bounds
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

noncomputable section
open BianchiIX

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

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_exitTailGap {R : ℝ → ℝ} {r s v : ℝ}
    (hR : HasDerivAt R r s) (hv : v ^ 2 < (R s) ^ 2) :
    HasDerivAt (fun q => exitTailGap (R q) v) (R s * r / exitTailGap (R s) v) s := by
  have ht : exitTailGap (R s) v ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (sub_pos.mpr hv))
  convert! ((hR.pow 2).sub_const (v ^ 2)).sqrt (ne_of_gt (sub_pos.mpr hv)) using 1
  norm_num only [Nat.reduceSub, pow_one, Pi.pow_apply, Nat.cast_ofNat]
  change R s * r / exitTailGap (R s) v = 2 * R s * r / (2 * exitTailGap (R s) v)
  field_simp

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_exitTail_radial {Y : ℝ → ExitTailState} {ξ : ExitTailState} {s v : ℝ}
    (hY : HasDerivAt Y ξ s) (hR : 0 < Y s 0) (hv : v ^ 2 < (Y s 0) ^ 2)
    (hd : exitTailSpeed (Y s 0) (Y s 1) v (Y s 2) ≠ 0) :
    HasDerivAt (fun q => exitTailRadial (Y q 0) (Y q 1) v (Y q 2))
      (∑ i : Fin 3, exitTailRadialGradient (Y s 0) (Y s 1) v (Y s 2) i * ξ i) s := by
  have h0 := hasDerivAt_pi.mp hY 0
  have h1 := hasDerivAt_pi.mp hY 1
  have h2 := hasDerivAt_pi.mp hY 2
  have ht := hasDerivAt_exitTailGap h0 hv
  have hc := h1.mul (((hasDerivAt_const s v).add h2).sub h1)
  have hs := ht.add hc
  have hn := (hc.neg.mul h0).sub ((ht.mul ((h1.sub h2).pow 2)).div h0 (ne_of_gt hR))
  have H := hn.div hs hd
  apply H.congr_deriv
  have ht0 : exitTailGap (Y s 0) v ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (sub_pos.mpr hv))
  simp [Fin.sum_univ_succ, exitTailRadialGradient, exitTailRadial, exitTailSpeed, coupling]
  dsimp only [exitTailSpeed, coupling] at hd
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_exitTail_strongRate {Y : ℝ → ExitTailState} {ξ : ExitTailState} {s v : ℝ}
    (hY : HasDerivAt Y ξ s) (hv : v ^ 2 < (Y s 0) ^ 2)
    (hd : exitTailSpeed (Y s 0) (Y s 1) v (Y s 2) ≠ 0) :
    HasDerivAt (fun q => exitTailStrongRate (Y q 0) (Y q 1) v (Y q 2))
      (∑ i : Fin 3, exitTailStrongRateGradient (Y s 0) (Y s 1) v (Y s 2) i * ξ i) s := by
  have h0 := hasDerivAt_pi.mp hY 0
  have h1 := hasDerivAt_pi.mp hY 1
  have h2 := hasDerivAt_pi.mp hY 2
  have ht := hasDerivAt_exitTailGap h0 hv
  have hc := h1.mul (((hasDerivAt_const s v).add h2).sub h1)
  have hs := ht.add hc
  have hn := (((ht.const_mul 2).sub (h0.pow 2)).add (h2.const_mul (2 * v))).sub (h2.pow 2) |>.add (h1.pow 2)
  have H := hn.div (hs.const_mul 2) (mul_ne_zero (by norm_num) hd)
  apply H.congr_deriv
  have ht0 : exitTailGap (Y s 0) v ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (sub_pos.mpr hv))
  simp [Fin.sum_univ_succ, exitTailStrongRateGradient, exitTailStrongRate, exitTailSpeed, coupling]
  dsimp only [exitTailSpeed, coupling] at hd
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_exitTail_weakRate {Y : ℝ → ExitTailState} {ξ : ExitTailState} {s v : ℝ}
    (hY : HasDerivAt Y ξ s) (hv : v ^ 2 < (Y s 0) ^ 2)
    (hd : exitTailSpeed (Y s 0) (Y s 1) v (Y s 2) ≠ 0) :
    HasDerivAt (fun q => exitTailWeakRate (Y q 0) (Y q 1) v (Y q 2))
      (∑ i : Fin 3, exitTailWeakRateGradient (Y s 0) (Y s 1) v (Y s 2) i * ξ i) s := by
  have h0 := hasDerivAt_pi.mp hY 0
  have h1 := hasDerivAt_pi.mp hY 1
  have h2 := hasDerivAt_pi.mp hY 2
  have ht := hasDerivAt_exitTailGap h0 hv
  have hc := h1.mul (((hasDerivAt_const s v).add h2).sub h1)
  have hs := ht.add hc
  have H := ((ht.sub_const 2).sub hc).div hs hd
  apply H.congr_deriv
  have ht0 : exitTailGap (Y s 0) v ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (sub_pos.mpr hv))
  simp [Fin.sum_univ_succ, exitTailWeakRateGradient, exitTailWeakRate, exitTailSpeed, coupling]
  dsimp only [exitTailSpeed, coupling] at hd
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_exitTailField {Y : ℝ → ExitTailState} {ξ : ExitTailState} {s v : ℝ}
    (hY : HasDerivAt Y ξ s) (hR : 0 < Y s 0) (hv : v ^ 2 < (Y s 0) ^ 2)
    (hd : exitTailSpeed (Y s 0) (Y s 1) v (Y s 2) ≠ 0) :
    HasDerivAt (fun q => exitTailField v (Y q)) (exitTailLinearization v (Y s) ξ) s := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hasDerivAt_exitTail_radial hY hR hv hd
  · convert! (hasDerivAt_exitTail_strongRate hY hv hd).mul (hasDerivAt_pi.mp hY 1) using 1
    dsimp [exitTailLinearization]
    ring
  · convert! (hasDerivAt_exitTail_weakRate hY hv hd).mul (hasDerivAt_pi.mp hY 2) using 1
    dsimp [exitTailLinearization]
    ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitTailField_fderiv {v : ℝ} {Y : ExitTailState} (hR : 0 < Y 0)
    (hv : v ^ 2 < (Y 0) ^ 2) (hd : exitTailSpeed (Y 0) (Y 1) v (Y 2) ≠ 0)
    (ξ : ExitTailState) : fderiv ℝ (exitTailField v) Y ξ = exitTailLinearization v Y ξ := by
  have hreg : ContDiffAt ℝ 1 (exitTailField v) Y :=
    (contDiffAt_exitTailField 1 hv (ne_of_gt hR) hd).comp Y (by fun_prop)
  have hline : HasDerivAt (fun s : ℝ => Y + s • ξ) ξ 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const ξ).const_add Y
  have hf : HasFDerivAt (exitTailField v) (fderiv ℝ (exitTailField v) Y) (Y + (0 : ℝ) • ξ) := by
    simpa using (hreg.differentiableAt (by norm_num)).hasFDerivAt
  have H := hf.comp_hasDerivAt 0 hline
  have K := hasDerivAt_exitTailField hline (by simpa using hR) (by simpa using hv) (by simpa using hd)
  simpa only [zero_smul, add_zero] using H.unique K

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitTailRateGradient_bounds {v : ℝ} {Y : ExitTailState}
    (hR : 7 / 4 ≤ Y 0 ∧ Y 0 ≤ 17 / 4) (hu : |Y 1| ≤ 1 / 100)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : |Y 2| ≤ 1 / 100) (i : Fin 2) :
    |exitTailRateGradient v Y i 0| ≤ 512 ∧
      ∀ j : Fin 2, |exitTailRateGradient v Y i j.succ| ≤ 256 * (v + |Y 1| + |Y 2|) := by
  have H := exitTail_rate_gradient_bounds hR hu hv hw
  fin_cases i
  · exact ⟨H.1, fun j => (H.2.2 j).1⟩
  · exact ⟨H.2.1, fun j => (H.2.2 j).2⟩

end
end

private theorem BianchiIX.abs_three_dot_le {a ξ : Fin 3 → ℝ} {A B C : ℝ}
    (h0 : |a 0| ≤ A) (h1 : |a 1| ≤ B) (h2 : |a 2| ≤ C) :
    |∑ i : Fin 3, a i * ξ i| ≤ (A + B + C) * ‖ξ‖ := by
  have hx (i : Fin 3) : |ξ i| ≤ ‖ξ‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm ξ i
  have H := Finset.abs_sum_le_sum_abs (fun i : Fin 3 => a i * ξ i) Finset.univ
  simp only [abs_mul] at H
  have H0 := mul_le_mul h0 (hx 0) (abs_nonneg _) ((abs_nonneg _).trans h0)
  have H1 := mul_le_mul h1 (hx 1) (abs_nonneg _) ((abs_nonneg _).trans h1)
  have H2 := mul_le_mul h2 (hx 2) (abs_nonneg _) ((abs_nonneg _).trans h2)
  simp [Fin.sum_univ_succ] at H ⊢
  nlinarith only [H, H0, H1, H2]


/-- Its integrable norm bound gives ordinary variational control without a long-time exponential loss. -/
theorem solution {v : ℝ} {Y : ExitTailState}
    (hR : 7 / 4 ≤ Y 0 ∧ Y 0 ≤ 17 / 4) (hu : |Y 1| ≤ 1 / 100)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : |Y 2| ≤ 1 / 100) :
    ‖fderiv ℝ (exitTailField v) Y‖ ≤
      |exitTailWallRate v Y 0| + |exitTailWallRate v Y 1| + 2048 * (v + |Y 1| + |Y 2|) := by
  let b := |Y 1| + |Y 2|
  let H := |Y 1| * v + b ^ 2
  have hb : 0 ≤ b := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hb1 : b ≤ 1 := by dsimp only [b]; linarith only [hu, hw]
  have hB : 0 ≤ v + b := add_nonneg hv.1 hb
  have hB2 : v + b ≤ 2 := by linarith only [hv.2, hb1]
  have hH : H ≤ v + b := by
    have HU : |Y 1| ≤ 1 := hu.trans (by norm_num)
    have Hv := mul_le_mul_of_nonneg_right HU hv.1
    have Hsq : b ^ 2 ≤ b := by nlinarith only [hb, hb1]
    dsimp only [H]
    nlinarith only [Hv, Hsq]
  have hR0 : 0 < Y 0 := by linarith only [hR.1]
  have hvR : v ^ 2 < (Y 0) ^ 2 := by nlinarith only [hR.1, hv.1, hv.2]
  have hd : exitTailSpeed (Y 0) (Y 1) v (Y 2) ≠ 0 := by
    have H := exitTailSpeed_compact hR.1 hu hv hw
    linarith only [H]
  have HR := exitTail_radial_gradient_bounds hR hu hv hw
  apply ContinuousLinearMap.opNorm_le_bound _ (by
    have H0 := abs_nonneg (exitTailWallRate v Y 0)
    have H1 := abs_nonneg (exitTailWallRate v Y 1)
    change 0 ≤ _ + _ + 2048 * (v + |Y 1| + |Y 2|)
    dsimp only [b] at hB
    linarith only [H0, H1, hB])
  intro ξ
  have hn : 0 ≤ ‖ξ‖ := norm_nonneg _
  have hrad : |∑ i : Fin 3, exitTailRadialGradient (Y 0) (Y 1) v (Y 2) i * ξ i| ≤
      512 * (v + b) * ‖ξ‖ := by
    have Hdot := abs_three_dot_le (ξ := ξ) HR.1 HR.2.1 HR.2.2
    have Hsum : 256 * H + 32 * (v + b) + 16 * b ≤ 512 * (v + b) := by
      linarith only [hH, hv.1, hb]
    have HH := mul_le_mul_of_nonneg_right Hsum hn
    dsimp only [H, b] at HH ⊢
    nlinarith only [Hdot, HH]
  have hrate (i : Fin 2) : |∑ j : Fin 3, exitTailRateGradient v Y i j * ξ j| ≤ 1536 * ‖ξ‖ := by
    have HI := exitTailRateGradient_bounds hR hu hv hw i
    have Hdot := abs_three_dot_le (ξ := ξ) HI.1 (HI.2 0) (HI.2 1)
    have Hsum : 512 + 256 * (v + b) + 256 * (v + b) ≤ 1536 := by linarith only [hB2]
    have HH := mul_le_mul_of_nonneg_right Hsum hn
    dsimp only [b] at HH
    nlinarith only [Hdot, HH]
  have hcoord (i : Fin 3) : |ξ i| ≤ ‖ξ‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm ξ i
  have hwall (i : Fin 2) :
      |Y i.succ * (∑ j : Fin 3, exitTailRateGradient v Y i j * ξ j) + exitTailWallRate v Y i * ξ i.succ| ≤
        (|exitTailWallRate v Y 0| + |exitTailWallRate v Y 1| + 2048 * (v + b)) * ‖ξ‖ := by
    have hYb : |Y i.succ| ≤ b := by fin_cases i <;> dsimp [b] <;> linarith [abs_nonneg (Y 1), abs_nonneg (Y 2)]
    have ha : |exitTailWallRate v Y i| ≤ |exitTailWallRate v Y 0| + |exitTailWallRate v Y 1| := by
      fin_cases i
      · exact le_add_of_nonneg_right (abs_nonneg (exitTailWallRate v Y 1))
      · exact le_add_of_nonneg_left (abs_nonneg (exitTailWallRate v Y 0))
    have H0 := mul_le_mul hYb (hrate i) (abs_nonneg _) hb
    have H1 := mul_le_mul ha (hcoord i.succ) (abs_nonneg _)
      (add_nonneg (abs_nonneg _) (abs_nonneg _))
    have Htri := abs_add_le
      (Y i.succ * (∑ j : Fin 3, exitTailRateGradient v Y i j * ξ j)) (exitTailWallRate v Y i * ξ i.succ)
    simp only [abs_mul] at Htri
    have Hsmall := mul_nonneg hv.1 hn
    have Hsmall' := mul_nonneg hb hn
    nlinarith only [Htri, H0, H1, Hsmall, Hsmall']
  rw [exitTailField_fderiv hR0 hvR hd]
  apply (pi_norm_le_iff_of_nonempty _).mpr
  intro i
  rw [Real.norm_eq_abs]
  fin_cases i
  · change |∑ i : Fin 3, exitTailRadialGradient (Y 0) (Y 1) v (Y 2) i * ξ i| ≤ _
    have HH : 512 * (v + b) ≤
        |exitTailWallRate v Y 0| + |exitTailWallRate v Y 1| + 2048 * (v + b) := by
      linarith only [hB, abs_nonneg (exitTailWallRate v Y 0), abs_nonneg (exitTailWallRate v Y 1)]
    have Hmul := mul_le_mul_of_nonneg_right HH hn
    dsimp only [b] at hrad Hmul
    nlinarith only [hrad, Hmul]
  · simpa [exitTailLinearization, exitTailRateGradient, exitTailWallRate, b, add_assoc] using hwall 0
  · simpa [exitTailLinearization, exitTailRateGradient, exitTailWallRate, b, add_assoc] using hwall 1
