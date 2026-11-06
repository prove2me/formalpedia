-- Prove2me | solution 1 for BianchiIX.exists_exitTail_uniform_variation_budget
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T19:00:38.796511+00:00
-- url     : https://prove2.me/submissions/95c85b98-9e07-44fd-a5a9-b0679ef8961e

import Definitions.Def_BianchiIX_TerminalConnectionData
import Definitions.Def_BianchiIX_TerminalConeData
import Theorems.Thm_BianchiIX_exists_exitTail_feedback_budget
import Theorems.Thm_BianchiIX_exists_exitTail_scale_bounds
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.ProjIcc
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Positivity

noncomputable section
open BianchiIX
open Set

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitTailLength_nonneg {η α : ℝ} (hη : 0 < η ∧ η ≤ 1) (hα : 0 < α ∧ α ≤ 1) (J : ℕ) :
    0 ≤ exitTailLength η α J := by
  have he : 0 ≤ Real.log (1 / η) := Real.log_nonneg ((le_div_iff₀ hη.1).mpr (by linarith only [hη.2]))
  have ha : 0 ≤ Real.log (1 / α) := Real.log_nonneg ((le_div_iff₀ hα.1).mpr (by linarith only [hα.2]))
  exact add_nonneg he (mul_nonneg (Nat.cast_nonneg _) ha)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.power_mul_log_inv_bound {α : ℝ} (hα : 0 < α) (J : ℕ) :
    α ^ J * ((J : ℝ) * Real.log (1 / α)) ≤ Real.exp (-1) := by
  have H := Real.mul_exp_neg_le_exp_neg_one ((J : ℝ) * Real.log (1 / α))
  have he : Real.exp (-((J : ℝ) * Real.log (1 / α))) = α ^ J := by
    rw [one_div, Real.log_inv, mul_neg, neg_neg, Real.exp_nat_mul, Real.exp_log hα]
  rw [he] at H
  linarith only [H]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.sq_mul_exp_neg_bound {x : ℝ} (hx : 0 ≤ x) :
    x ^ 2 * Real.exp (-x) ≤ 4 * Real.exp (-2) := by
  have H := Real.mul_exp_neg_le_exp_neg_one (x / 2)
  have hpos : 0 ≤ x / 2 * Real.exp (-(x / 2)) := mul_nonneg (by positivity) (Real.exp_pos _).le
  have Hsq := (sq_le_sq₀ hpos (Real.exp_pos _).le).mpr H
  have h1 : Real.exp (-(x / 2)) ^ 2 = Real.exp (-x) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have h2 : Real.exp (-1) ^ 2 = Real.exp (-2) := by rw [sq, ← Real.exp_add]; norm_num
  rw [mul_pow, h1, h2] at Hsq
  nlinarith only [Hsq]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitTailLength_weighted_bounds {η α : ℝ} (hη : 0 < η ∧ η ≤ 1)
    (hα : 0 < α ∧ α ≤ 1) (J : ℕ) :
    α * exitTailLength η α J ≤ Real.log (1 / η) + J * Real.exp (-1) ∧
    α ^ J * (1 + exitTailLength η α J) ≤ 1 + Real.log (1 / η) + Real.exp (-1) ∧
    α ^ J * (1 + exitTailLength η α J) ^ 2 ≤
      2 * (1 + Real.log (1 / η)) ^ 2 + 8 * Real.exp (-2) := by
  have he : 0 ≤ Real.log (1 / η) := Real.log_nonneg ((le_div_iff₀ hη.1).mpr (by linarith only [hη.2]))
  have ha : 0 ≤ Real.log (1 / α) := Real.log_nonneg ((le_div_iff₀ hα.1).mpr (by linarith only [hα.2]))
  have hp0 := pow_nonneg hα.1.le J
  have hp1 : α ^ J ≤ 1 := pow_le_one₀ hα.1.le hα.2
  have H1 := power_mul_log_inv_bound hα.1 1
  simp only [pow_one, Nat.cast_one, one_mul] at H1
  have HJ := power_mul_log_inv_bound hα.1 J
  have Hsq := sq_mul_exp_neg_bound (mul_nonneg (Nat.cast_nonneg J) ha)
  have hExp : Real.exp (-((J : ℝ) * Real.log (1 / α))) = α ^ J := by
    rw [one_div, Real.log_inv, mul_neg, neg_neg, Real.exp_nat_mul, Real.exp_log hα.1]
  rw [hExp] at Hsq
  refine ⟨?_, ?_, ?_⟩
  · dsimp only [exitTailLength]
    nlinarith only [mul_le_mul_of_nonneg_right hα.2 he,
      mul_le_mul_of_nonneg_left H1 (Nat.cast_nonneg J)]
  · dsimp only [exitTailLength]
    nlinarith only [HJ, mul_le_mul_of_nonneg_right hp1 (by positivity : 0 ≤ 1 + Real.log (1 / η))]
  · have Hsplit : (1 + exitTailLength η α J) ^ 2 ≤
        2 * (1 + Real.log (1 / η)) ^ 2 + 2 * ((J : ℝ) * Real.log (1 / α)) ^ 2 := by
      dsimp only [exitTailLength]
      nlinarith only [sq_nonneg (1 + Real.log (1 / η) - J * Real.log (1 / α))]
    have H := mul_le_mul_of_nonneg_left Hsplit hp0
    have HB := mul_le_mul_of_nonneg_right hp1 (sq_nonneg (1 + Real.log (1 / η)))
    nlinarith only [H, HB, Hsq]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitTail_smallness_budgets {η α ε b : ℝ} {J : ℕ}
    (hη : 0 < η ∧ η ≤ 1) (hα : 0 < α ∧ α ≤ 1) (hε : 0 ≤ ε)
    (hJ : 1 ≤ J) (hb : b ≤ ε * α ^ J) :
    b * (1 + exitTailLength η α J) ≤ ε * (1 + Real.log (1 / η) + Real.exp (-1)) ∧
    b / (η * α ^ J) ≤ ε / η ∧ b / α ≤ ε * α ^ (J - 1) := by
  have HL := exitTailLength_weighted_bounds hη hα J
  refine ⟨?_, ?_, ?_⟩
  · have H := mul_le_mul_of_nonneg_right hb
      (show 0 ≤ 1 + exitTailLength η α J by linarith only [exitTailLength_nonneg hη hα J])
    have H' := mul_le_mul_of_nonneg_left HL.2.1 hε
    nlinarith only [H, H']
  · apply (div_le_iff₀ (mul_pos hη.1 (pow_pos hα.1 J))).mpr
    convert! hb using 1
    field_simp [ne_of_gt hη.1]
  · apply (div_le_iff₀ hα.1).mpr
    have hp : α ^ J = α ^ (J - 1) * α := by
      rw [← pow_succ, Nat.sub_add_cancel hJ]
    simpa only [hp, mul_assoc] using hb

end
end


theorem solution {η : ℝ} (hη : 0 < η ∧ η ≤ 1)
    {J : ℕ} (hJ : 1 ≤ J) :
    ∃ A ≥ (2 : ℝ), ∃ B ≥ (0 : ℝ), ∃ ε > (0 : ℝ),
      ∀ (α b T : ℝ) (Y : ℝ → ExitTailState),
      (0 < α ∧ α ≤ 1) → 0 < b → b ≤ ε * α ^ J →
      (0 ≤ T ∧ T ≤ exitTailLength η α J) → Y 0 0 = 2 + 2 * α →
      |Y 0 1| + |Y 0 2| ≤ b →
      (∀ s ∈ Icc 0 T, HasDerivAt Y (exitTailField (Real.exp (-s)) (Y s)) s) →
      (∀ s ∈ Icc 0 T, exitTailRegion α b A (80 * A) (Y s)) ∧
        exitTailVariationBudget α b A (80 * A) T ≤ B := by
  let K := Real.log (1 / η) + J * Real.exp (-1)
  let Q := 1 + Real.log (1 / η) + Real.exp (-1)
  have he : 0 ≤ Real.log (1 / η) := Real.log_nonneg
    ((le_div_iff₀ hη.1).mpr (by linarith only [hη.2]))
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hQ : 0 < Q := by dsimp only [Q]; positivity
  obtain ⟨A, hA, ε₀, hε₀, HP⟩ := exists_exitTail_scale_bounds hη hJ
  have hA0 : 0 ≤ A := by linarith only [hA]
  obtain ⟨δ, hδ, hδ1, HB⟩ := exists_exitTail_feedback_budget
    (by linarith only [hA] : 1 ≤ A) (by positivity : 0 ≤ 80 * A)
  let B := 2 * (10 * K + 6) + 2048 * (1 + A)
  let ε := min ε₀ (δ / Q)
  have hε : 0 < ε := lt_min hε₀ (div_pos hδ hQ)
  refine ⟨A, hA, B, by dsimp only [B]; positivity, ε, hε, ?_⟩
  intro α b T Y hα hb hsmall hT hR hw hY
  have hsmall₀ : b ≤ ε₀ * α ^ J := hsmall.trans
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (pow_nonneg hα.1.le J))
  have Hpath := HP α b T Y hα hb hsmall₀ hT hR hw hY
  have Hscale := (exitTail_smallness_budgets hη hα hε.le hJ hsmall).1
  have Hδ : ε * Q ≤ δ := (le_div_iff₀ hQ).mp (min_le_right _ _)
  have Hsmall : b * (1 + T) ≤ δ :=
    (mul_le_mul_of_nonneg_left (add_le_add le_rfl hT.2) hb.le).trans (Hscale.trans Hδ)
  have Hwait := (exitTailLength_weighted_bounds hη hα J).1
  have Hrate := (HB T b α K hT.1 hb.le Hsmall
    ((mul_le_mul_of_nonneg_left hT.2 hα.1.le).trans Hwait)).1
  have HbT : b * T ≤ 1 := by nlinarith only [Hsmall, hδ1, hb]
  have HAbT := mul_le_mul_of_nonneg_left HbT hA0
  refine ⟨fun s hs => (Hpath s hs).1, ?_⟩
  dsimp only [exitTailVariationBudget, B]
  nlinarith only [Hrate, HAbT]
