-- Prove2me | solution 1 for BianchiIX.exists_exitTail_strict_prefix_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T17:58:38.545074+00:00
-- url     : https://prove2.me/submissions/7f2c163e-5f71-407a-9688-97f7aa4641fe

import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_TerminalConnectionData
import Theorems.Thm_BianchiIX_abs_sub_le_integral_bound
import Theorems.Thm_BianchiIX_exists_exitTail_feedback_budget
import Theorems.Thm_BianchiIX_exitTail_boundary_rate_small
import Theorems.Thm_BianchiIX_exitTail_perturbation_bounds
import Theorems.Thm_BianchiIX_homogeneous_solution_eq_exp_integral_Icc
import Theorems.Thm_BianchiIX_integral_exp_decay
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
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral

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
open Set MeasureTheory

private theorem BianchiIX.integral_exp_decay_le {a b c : ℝ} (hc : 0 < c) :
    (∫ z in a..b, Real.exp (-c * (z - a))) ≤ 1 / c := by
  rw [integral_exp_decay hc]
  exact (div_le_div_iff_of_pos_right hc).mpr (by linarith [Real.exp_pos (-c * (b - a))])

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.integral_exit_tail_envelope {T A B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) :
    (∫ s in (0 : ℝ)..T, A + B * Real.exp (-s) + C * Real.exp (-2 * s)) ≤ A * T + B + C / 2 := by
  have h0 : IntervalIntegrable (fun _ : ℝ => A) volume 0 T := intervalIntegrable_const
  have h1 : IntervalIntegrable (fun s => B * Real.exp (-s)) volume 0 T :=
    (by fun_prop : Continuous (fun s : ℝ => B * Real.exp (-s))).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun s => C * Real.exp (-2 * s)) volume 0 T :=
    (by fun_prop : Continuous (fun s : ℝ => C * Real.exp (-2 * s))).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (h0.add h1) h2, intervalIntegral.integral_add h0 h1,
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have H1 := integral_exp_decay_le (a := 0) (b := T) (by norm_num : (0 : ℝ) < 1)
  have H2 := integral_exp_decay_le (a := 0) (b := T) (by norm_num : (0 : ℝ) < 2)
  simp only [sub_zero, neg_mul, one_mul, one_div_one] at H1 H2
  simp only [sub_zero, smul_eq_mul, neg_mul]
  nlinarith only [mul_le_mul_of_nonneg_left H1 hB, mul_le_mul_of_nonneg_left H2 hC]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.integral_abs_le_exit_tail_envelope {f : ℝ → ℝ} {T A B C : ℝ} (hT : 0 ≤ T)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hf : ContinuousOn f (Icc 0 T))
    (hbound : ∀ s ∈ Icc 0 T, |f s| ≤ A + B * Real.exp (-s) + C * Real.exp (-2 * s)) :
    (∫ s in (0 : ℝ)..T, |f s|) ≤ A * T + B + C / 2 := by
  have hc : Continuous (fun s : ℝ => A + B * Real.exp (-s) + C * Real.exp (-2 * s)) := by fun_prop
  exact (intervalIntegral.integral_mono_on hT (hf.abs.intervalIntegrable_of_Icc hT)
    (hc.intervalIntegrable _ _) hbound).trans (integral_exit_tail_envelope hB hC)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.exitTailField_wall (v : ℝ) (Y : ExitTailState) (i : Fin 2) :
    exitTailField v Y i.succ = exitTailWallRate v Y i * Y i.succ := by
  fin_cases i <;> rfl

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.continuousOn_exitTailWallRate {Y : ℝ → ExitTailState} {I : Set ℝ}
    (hY : ContinuousOn Y I)
    (hd : ∀ s ∈ I, exitTailSpeed (Y s 0) (Y s 1) (Real.exp (-s)) (Y s 2) ≠ 0)
    (i : Fin 2) : ContinuousOn (fun s => exitTailWallRate (Real.exp (-s)) (Y s) i) I := by
  have hy (j : Fin 3) : ContinuousOn (fun s => Y s j) I :=
    (continuous_apply j).comp_continuousOn hY
  have hv : ContinuousOn (fun s : ℝ => Real.exp (-s)) I := by fun_prop
  have ht : ContinuousOn (fun s => exitTailGap (Y s 0) (Real.exp (-s))) I :=
    (((hy 0).pow 2).sub (hv.pow 2)).sqrt
  have hc : ContinuousOn (fun s => coupling (Y s 1) (Real.exp (-s)) (Y s 2)) I :=
    (hy 1).mul ((hv.add (hy 2)).sub (hy 1))
  have hs : ContinuousOn (fun s => exitTailSpeed (Y s 0) (Y s 1) (Real.exp (-s)) (Y s 2)) I := ht.add hc
  fin_cases i
  · change ContinuousOn (fun s => exitTailStrongRate (Y s 0) (Y s 1) (Real.exp (-s)) (Y s 2)) I
    have hbase := (ht.const_mul 2).sub ((hy 0).pow 2)
    have hcross := (hv.const_mul 2).mul (hy 2)
    have hn := ((hbase.add hcross).sub ((hy 2).pow 2)).add ((hy 1).pow 2)
    exact hn.div (hs.const_mul 2)
      (fun s hs => mul_ne_zero (by norm_num) (hd s hs))
  · change ContinuousOn (fun s => exitTailWeakRate (Y s 0) (Y s 1) (Real.exp (-s)) (Y s 2)) I
    exact ((ht.sub continuousOn_const).sub hc).div hs hd

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.exitTail_wall_multiplier {Y : ℝ → ExitTailState} {T : ℝ} (hT : 0 ≤ T)
    (hY : ∀ s ∈ Icc 0 T, HasDerivAt Y (exitTailField (Real.exp (-s)) (Y s)) s)
    (hd : ∀ s ∈ Icc 0 T, exitTailSpeed (Y s 0) (Y s 1) (Real.exp (-s)) (Y s 2) ≠ 0)
    (i : Fin 2) :
    Y T i.succ = Y 0 i.succ * exitTailMultiplier Y i T ∧ 0 < exitTailMultiplier Y i T := by
  have hy := HasDerivAt.continuousOn hY
  refine ⟨?_, Real.exp_pos _⟩
  apply homogeneous_solution_eq_exp_integral_Icc hT (continuousOn_exitTailWallRate hy hd i)
    ((continuous_apply i.succ).comp_continuousOn hy)
  intro s hs
  have H := hasDerivAt_pi.mp (hY s (Ioo_subset_Icc_self hs)) i.succ
  rw [exitTailField_wall] at H
  exact H

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.exitTailWallRate_abs {α v : ℝ} {Y : ExitTailState} (hα : 0 ≤ α)
    (hR : 7 / 4 ≤ Y 0 ∧ Y 0 ≤ 17 / 4) (hu : |Y 1| ≤ 1 / 100)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : |Y 2| ≤ 1 / 100) (i : Fin 2) :
    |exitTailWallRate v Y i| ≤ 10 * (α + |Y 0 - (2 + 2 * α)| + v ^ 2) +
      100 * ((|Y 1| + |Y 2|) * v + (|Y 1| + |Y 2|) ^ 2) := by
  have Hp := exitTail_perturbation_bounds hR hu hv hw
  have Hb := exitTail_boundary_rate_small hα hR hv
  fin_cases i
  · change |exitTailStrongRate (Y 0) (Y 1) v (Y 2)| ≤ _
    have H := abs_sub_le (exitTailStrongRate (Y 0) (Y 1) v (Y 2)) (exitTailStrongRate (Y 0) 0 v 0) 0
    simp only [sub_zero] at H
    linarith only [H, Hp.2.1, Hb, abs_nonneg (exitTailWeakRate (Y 0) 0 v 0)]
  · change |exitTailWeakRate (Y 0) (Y 1) v (Y 2)| ≤ _
    have H := abs_sub_le (exitTailWeakRate (Y 0) (Y 1) v (Y 2)) (exitTailWeakRate (Y 0) 0 v 0) 0
    simp only [sub_zero] at H
    linarith only [H, Hp.2.2, Hb, abs_nonneg (exitTailStrongRate (Y 0) 0 v 0)]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.exitTail_rate_integral_bound {Y : ℝ → ExitTailState} {T α b A D : ℝ}
    (hT : 0 ≤ T) (hα : 0 ≤ α) (hb : 0 ≤ b) (hA : 0 ≤ A)
    (hY : ContinuousOn Y (Icc 0 T))
    (hreg : ∀ s ∈ Icc 0 T, exitTailRegion α b A D (Y s)) (i : Fin 2) :
    |∫ s in (0 : ℝ)..T, exitTailWallRate (Real.exp (-s)) (Y s) i| ≤ exitTailRateBudget α b A D T := by
  have hv (s : ℝ) (hs : s ∈ Icc 0 T) : 0 ≤ Real.exp (-s) ∧ Real.exp (-s) ≤ 1 :=
    ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs.1)⟩
  have hd (s : ℝ) (hs : s ∈ Icc 0 T) : exitTailSpeed (Y s 0) (Y s 1) (Real.exp (-s)) (Y s 2) ≠ 0 := by
    have H := exitTailSpeed_compact (hreg s hs).1.1 (hreg s hs).2.1 (hv s hs) (hreg s hs).2.2.1
    linarith only [H]
  have hc := continuousOn_exitTailWallRate hY hd i
  have H := integral_abs_le_exit_tail_envelope hT (by positivity : 0 ≤ 100 * A * b)
    (by norm_num : (0 : ℝ) ≤ 10) hc (A := 10 * (α + D * b) + 100 * (A * b) ^ 2) ?_
  · apply (intervalIntegral.abs_integral_le_integral_abs hT).trans
    simpa only [exitTailRateBudget, show (10 : ℝ) / 2 = 5 by norm_num] using H
  · intro s hs
    obtain ⟨hR, hu, hw, hsum, hrad⟩ := hreg s hs
    have H' := exitTailWallRate_abs hα hR hu (hv s hs) hw i
    have hsq := (sq_le_sq₀ (add_nonneg (abs_nonneg _) (abs_nonneg _)) (mul_nonneg hA hb)).mpr hsum
    have hm := mul_le_mul_of_nonneg_right hsum (hv s hs).1
    have he : Real.exp (-s) ^ 2 = Real.exp (-2 * s) := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    rw [he] at H'
    nlinarith only [H', hsq, hm, hrad]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.exitTail_prefix_multipliers {Y : ℝ → ExitTailState} {T α b A D : ℝ}
    (hT : 0 ≤ T) (hα : 0 ≤ α) (hb : 0 ≤ b) (hA : 0 ≤ A)
    (hY : ∀ s ∈ Icc 0 T, HasDerivAt Y (exitTailField (Real.exp (-s)) (Y s)) s)
    (hreg : ∀ s ∈ Icc 0 T, exitTailRegion α b A D (Y s)) (i : Fin 2) :
    Y T i.succ = Y 0 i.succ * exitTailMultiplier Y i T ∧
      Real.exp (-exitTailRateBudget α b A D T) ≤ exitTailMultiplier Y i T ∧
      exitTailMultiplier Y i T ≤ Real.exp (exitTailRateBudget α b A D T) := by
  have hd (s : ℝ) (hs : s ∈ Icc 0 T) : exitTailSpeed (Y s 0) (Y s 1) (Real.exp (-s)) (Y s 2) ≠ 0 := by
    have hv : 0 ≤ Real.exp (-s) ∧ Real.exp (-s) ≤ 1 :=
      ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs.1)⟩
    have H := exitTailSpeed_compact (hreg s hs).1.1 (hreg s hs).2.1 hv (hreg s hs).2.2.1
    linarith only [H]
  have H := exitTail_rate_integral_bound hT hα hb hA (HasDerivAt.continuousOn hY) hreg i
  exact ⟨(exitTail_wall_multiplier hT hY hd i).1,
    Real.exp_le_exp.mpr (abs_le.mp H).1, Real.exp_le_exp.mpr (abs_le.mp H).2⟩

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.exitTail_prefix_radial_bound {Y : ℝ → ExitTailState} {T α b A D : ℝ}
    (hT : 0 ≤ T) (hb : 0 ≤ b) (hA : 0 ≤ A)
    (hY : ∀ s ∈ Icc 0 T, HasDerivAt Y (exitTailField (Real.exp (-s)) (Y s)) s)
    (hreg : ∀ s ∈ Icc 0 T, exitTailRegion α b A D (Y s)) :
    |Y T 0 - Y 0 0| ≤ 20 * (A * b + (A * b) ^ 2 * T) := by
  have H := abs_sub_le_integral_bound hT
    (fun s hs => hasDerivAt_pi.mp (hY s hs) 0)
    (B := fun s => 20 * (A * b) ^ 2 + (20 * A * b) * Real.exp (-s) + 0 * Real.exp (-2 * s))
    (by fun_prop) ?_
  · have HI := integral_exit_tail_envelope (T := T) (A := 20 * (A * b) ^ 2)
      (by positivity : 0 ≤ 20 * A * b) (by norm_num : (0 : ℝ) ≤ 0)
    exact H.trans (HI.trans_eq (by ring))
  · intro s hs
    obtain ⟨hR, hu, hw, hsum, _⟩ := hreg s hs
    have hv : 0 ≤ Real.exp (-s) ∧ Real.exp (-s) ≤ 1 :=
      ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs.1)⟩
    have Hp := (exitTail_perturbation_bounds hR hu hv hw).1
    have hsq := (sq_le_sq₀ (add_nonneg (abs_nonneg _) (abs_nonneg _)) (mul_nonneg hA hb)).mpr hsum
    have hU : |Y s 1| ≤ A * b := by linarith only [hsum, abs_nonneg (Y s 2)]
    have hm := mul_le_mul_of_nonneg_right hU hv.1
    change |exitTailRadial (Y s 0) (Y s 1) (Real.exp (-s)) (Y s 2)| ≤ _
    nlinarith only [Hp, hsq, hm]

end
end


/-- A single smallness budget improves both wall and radial bootstrap constants by a factor of two. -/
theorem solution {K : ℝ} (hK : 0 ≤ K) :
    ∃ A ≥ (2 : ℝ), ∃ ε > (0 : ℝ), ε ≤ 1 ∧ ∀ T α b : ℝ, ∀ Y : ℝ → ExitTailState,
      0 ≤ T → 0 ≤ α → 0 ≤ b → b * (1 + T) ≤ ε → α * T ≤ K →
      (∀ s ∈ Icc 0 T, HasDerivAt Y (exitTailField (Real.exp (-s)) (Y s)) s) →
      (∀ s ∈ Icc 0 T, exitTailRegion α b A (80 * A) (Y s)) →
      |Y 0 1| + |Y 0 2| ≤ b →
      (∀ i : Fin 2,
        Y T i.succ = Y 0 i.succ * exitTailMultiplier Y i T ∧
        2 / A ≤ exitTailMultiplier Y i T ∧ exitTailMultiplier Y i T ≤ A / 2) ∧
      |Y T 1| + |Y T 2| ≤ A * b / 2 ∧ |Y T 0 - Y 0 0| ≤ 40 * A * b := by
  let L := 10 * K + 6
  let A := 2 * Real.exp L
  have hL : 0 ≤ L := by dsimp only [L]; linarith only [hK]
  have hA : 2 ≤ A := by
    have H : 1 ≤ Real.exp L := Real.one_le_exp_iff.mpr hL
    dsimp only [A]
    linarith only [H]
  have hA0 : 0 ≤ A := by linarith only [hA]
  obtain ⟨ε, hε, hε1, HB⟩ := exists_exitTail_feedback_budget
    (by linarith only [hA] : 1 ≤ A) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 80) hA0)
  refine ⟨A, hA, ε, hε, hε1, ?_⟩
  intro T α b Y hT hα hb hsmall hwait hY hreg hinit
  obtain ⟨hrate, hrad⟩ := HB T b α K hT hb hsmall hwait
  have hmult (i : Fin 2) : Y T i.succ = Y 0 i.succ * exitTailMultiplier Y i T ∧
      2 / A ≤ exitTailMultiplier Y i T ∧ exitTailMultiplier Y i T ≤ A / 2 := by
    obtain ⟨heq, hlo, hhi⟩ := exitTail_prefix_multipliers hT hα hb hA0 hY hreg i
    refine ⟨heq, ?_, ?_⟩
    · have H := (Real.exp_le_exp.mpr (neg_le_neg hrate)).trans hlo
      have he : Real.exp (-L) = 2 / A := by
        rw [Real.exp_neg]
        dsimp only [A]
        field_simp
      exact he ▸ H
    · have H := hhi.trans (Real.exp_le_exp.mpr hrate)
      have he : Real.exp L = A / 2 := by dsimp only [A]; ring
      exact H.trans_eq he
  refine ⟨hmult, ?_, (exitTail_prefix_radial_bound hT hb hA0 hY hreg).trans hrad⟩
  obtain ⟨he0, _, hi0⟩ := hmult 0
  obtain ⟨he1, _, hi1⟩ := hmult 1
  change Y T 1 = Y 0 1 * exitTailMultiplier Y 0 T at he0
  change Y T 2 = Y 0 2 * exitTailMultiplier Y 1 T at he1
  rw [he0, he1, abs_mul, abs_mul,
    abs_of_pos (show 0 < exitTailMultiplier Y 0 T from Real.exp_pos _),
    abs_of_pos (show 0 < exitTailMultiplier Y 1 T from Real.exp_pos _)]
  have H0 := mul_le_mul_of_nonneg_left hi0 (abs_nonneg (Y 0 1))
  have H1 := mul_le_mul_of_nonneg_left hi1 (abs_nonneg (Y 0 2))
  have H := mul_le_mul_of_nonneg_right hinit (by positivity : 0 ≤ A / 2)
  nlinarith only [H0, H1, H]
