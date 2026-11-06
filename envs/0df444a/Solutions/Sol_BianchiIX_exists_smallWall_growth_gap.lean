-- Prove2me | solution 1 for BianchiIX.exists_smallWall_growth_gap
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T04:06:16.942769+00:00
-- url     : https://prove2.me/submissions/8eeaa9d2-1127-416f-bc9d-176687cfe8c5

import Definitions.Def_BianchiIX_AxisAndOrbitData
import Definitions.Def_BianchiIX_GeometricExceptionData
import Theorems.Thm_BianchiIX_contDiff_stateConstraint
import Theorems.Thm_BianchiIX_normalizedState_norm_bound_abs
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Order.Compact

noncomputable section
open BianchiIX
open Set

section
noncomputable section
open BianchiIX

private theorem BianchiIX.kasner_rate_sum_product {p s : ℝ} (h : shearSq p s = 1) :
    rateOne p s + rateTwo p s + rateThree p s = -3 ∧
      rateOne p s * rateTwo p s * rateThree p s = 2 * (2 * p - 1) ^ 2 * (p + 1) := by
  have hsqrt : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hcircle : p ^ 2 + s ^ 2 = 1 := h
  dsimp only [rateOne, rateTwo, rateThree]
  rw [h]
  constructor
  · ring
  · calc
      (-1 + 2 * p) * (-1 - p + Real.sqrt 3 * s) * (-1 - p - Real.sqrt 3 * s) =
          (2 * p - 1) * ((1 + p) ^ 2 - 3 * s ^ 2) := by
            ring_nf
            rw [hsqrt]
            ring
      _ = (2 * p - 1) * (2 * (2 * p - 1) * (p + 1)) := by
        congr 1
        nlinarith only [hcircle]
      _ = 2 * (2 * p - 1) ^ 2 * (p + 1) := by ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.kasner_growth_signs {p s : ℝ} (h : shearSq p s = 1)
    (hp : p ≠ -1) (hp' : p ≠ 1 / 2) :
    (0 < rateOne p s ∧ rateTwo p s < 0 ∧ rateThree p s < 0) ∨
      (rateOne p s < 0 ∧ 0 < rateTwo p s ∧ rateThree p s < 0) ∨
      (rateOne p s < 0 ∧ rateTwo p s < 0 ∧ 0 < rateThree p s) := by
  obtain ⟨hsum, hprod⟩ := kasner_rate_sum_product h
  have hcircle : p ^ 2 + s ^ 2 = 1 := h
  have hlo : -1 < p := lt_of_le_of_ne (by nlinarith only [hcircle, sq_nonneg s]) (Ne.symm hp)
  have hsq : 0 < (2 * p - 1) ^ 2 := sq_pos_of_ne_zero (by intro heq; apply hp'; linarith only [heq])
  have hpositive : 0 < rateOne p s * rateTwo p s * rateThree p s := by
    rw [hprod]
    exact mul_pos (mul_pos (by norm_num) hsq) (by linarith only [hlo])
  rcases mul_pos_iff.mp hpositive with ⟨hab, hc⟩ | ⟨hab, hc⟩
  · rcases mul_pos_iff.mp hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · linarith only [hsum, ha, hb, hc]
    · exact Or.inr (Or.inr ⟨ha, hb, hc⟩)
  · rcases mul_neg_iff.mp hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact Or.inl ⟨ha, hb, hc⟩
    · exact Or.inr (Or.inl ⟨ha, hb, hc⟩)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.continuous_wallRate (i : Fin 3) : Continuous (wallRate i) := by
  change Continuous (fun x => wallRate i x)
  fin_cases i <;> dsimp [wallRate, rateOne, rateTwo, rateThree, shearSq] <;> fun_prop

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.continuous_normalizedEuclideanDistance :
    Continuous (fun p : NormalizedState × NormalizedState => normalizedEuclideanDistance p.1 p.2) := by
  unfold normalizedEuclideanDistance
  fun_prop

end
end

private theorem BianchiIX.continuous_wallGrowthMargin : Continuous wallGrowthMargin := by
  exact ((continuous_wallRate 0).min ((continuous_wallRate 1).neg.min (continuous_wallRate 2).neg)).max
    (((continuous_wallRate 1).min ((continuous_wallRate 0).neg.min (continuous_wallRate 2).neg)).max
      ((continuous_wallRate 2).min ((continuous_wallRate 0).neg.min (continuous_wallRate 1).neg)))

private theorem BianchiIX.exists_wall_rate_margin_of_le {x : NormalizedState} {c : ℝ} (h : c ≤ wallGrowthMargin x) :
    ∃ i : Fin 3, c ≤ wallRate i x ∧ ∀ j : Fin 3, j ≠ i → wallRate j x ≤ -c := by
  rcases le_max_iff.mp h with h | h
  · obtain ⟨h0, h1, h2⟩ := (le_min_iff.mp h).imp_right le_min_iff.mp
    refine ⟨0, h0, ?_⟩
    intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · simpa only [neg_neg] using! neg_le_neg h1
    · simpa only [neg_neg] using! neg_le_neg h2
  · rcases le_max_iff.mp h with h | h
    · obtain ⟨h1, h0, h2⟩ := (le_min_iff.mp h).imp_right le_min_iff.mp
      refine ⟨1, h1, ?_⟩
      intro j hj
      fin_cases j
      · simpa only [neg_neg] using! neg_le_neg h0
      · exact (hj rfl).elim
      · simpa only [neg_neg] using! neg_le_neg h2
    · obtain ⟨h2, h0, h1⟩ := (le_min_iff.mp h).imp_right le_min_iff.mp
      refine ⟨2, h2, ?_⟩
      intro j hj
      fin_cases j
      · simpa only [neg_neg] using! neg_le_neg h0
      · simpa only [neg_neg] using! neg_le_neg h1
      · exact (hj rfl).elim

private theorem BianchiIX.normalized_kasner_growth_margin_pos {x : NormalizedState}
    (hc : stateConstraint x = 1) (h2 : x 2 = 0) (h3 : x 3 = 0) (h4 : x 4 = 0)
    (hnot : ∀ i : Fin 3, x ≠ taubPoint i) : 0 < wallGrowthMargin x := by
  have hcircle : shearSq (x 0) (x 1) = 1 := by
    simpa only [stateConstraint, constraint, curvature, h2, h3, h4, zero_pow (by omega : 2 ≠ 0),
      mul_zero, zero_mul, add_zero, sub_zero] using hc
  have hsq : x 0 ^ 2 + x 1 ^ 2 = 1 := hcircle
  have hsqrt : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hp : x 0 ≠ -1 := by
    intro heq
    have hs : x 1 = 0 := by nlinarith only [hsq, heq]
    apply hnot 0
    change x = ![-1, 0, 0, 0, 0]
    ext j
    fin_cases j <;> first | exact heq | exact hs | exact h2 | exact h3 | exact h4
  have hp' : x 0 ≠ 1 / 2 := by
    intro heq
    have hfactor : (x 1 - Real.sqrt 3 / 2) * (x 1 + Real.sqrt 3 / 2) = 0 := by
      nlinarith only [hsq, heq, hsqrt]
    rcases mul_eq_zero.mp hfactor with hs | hs
    · have hs' : x 1 = Real.sqrt 3 / 2 := by linarith only [hs]
      apply hnot 2
      change x = ![1 / 2, Real.sqrt 3 / 2, 0, 0, 0]
      ext j
      fin_cases j <;> first | exact heq | exact hs' | exact h2 | exact h3 | exact h4
    · have hs' : x 1 = -Real.sqrt 3 / 2 := by linarith only [hs]
      apply hnot 1
      change x = ![1 / 2, -Real.sqrt 3 / 2, 0, 0, 0]
      ext j
      fin_cases j <;> first | exact heq | exact hs' | exact h2 | exact h3 | exact h4
  rcases kasner_growth_signs hcircle hp hp' with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
  · exact lt_max_of_lt_left (lt_min h0 (lt_min (neg_pos.mpr h1) (neg_pos.mpr h2)))
  · exact lt_max_of_lt_right (lt_max_of_lt_left (lt_min h1 (lt_min (neg_pos.mpr h0) (neg_pos.mpr h2))))
  · exact lt_max_of_lt_right (lt_max_of_lt_right (lt_min h2 (lt_min (neg_pos.mpr h0) (neg_pos.mpr h1))))


/-- Uniformly away from Taub, all sufficiently small-wall states have one growing and two decaying walls. -/
theorem solution {ε : ℝ} (hε : 0 < ε) :
    ∃ ν > (0 : ℝ), ν ≤ 1 / 4 ∧ ∃ c > (0 : ℝ), c ≤ 1 ∧
      ∀ x : NormalizedState, stateConstraint x = 1 →
        (∀ i : Fin 3, wallValue i x ∈ Icc 0 ν) →
        (∀ i : Fin 3, ε ≤ normalizedEuclideanDistance x (taubPoint i)) →
        ∃ i : Fin 3, c ≤ wallRate i x ∧ ∀ j : Fin 3, j ≠ i → wallRate j x ≤ -c := by
  let K : Set NormalizedState := {x | stateConstraint x = 1 ∧
    (∀ i : Fin 3, wallValue i x ∈ Icc 0 1) ∧
    ∀ i : Fin 3, ε ≤ normalizedEuclideanDistance x (taubPoint i)}
  have hKw : IsClosed {x : NormalizedState | ∀ i : Fin 3, wallValue i x ∈ Icc 0 1} := by
    simp only [ofPred_forall]
    exact isClosed_iInter (fun i => isClosed_Icc.preimage (continuous_apply (i.addNat 2)))
  have hKd : IsClosed {x : NormalizedState | ∀ i : Fin 3, ε ≤ normalizedEuclideanDistance x (taubPoint i)} := by
    have hd (i : Fin 3) : Continuous (fun x : NormalizedState => normalizedEuclideanDistance x (taubPoint i)) :=
      continuous_normalizedEuclideanDistance.comp (f := fun x : NormalizedState => (x, taubPoint i))
        (continuous_id.prodMk continuous_const)
    simp only [ofPred_forall]
    exact isClosed_iInter (fun i => isClosed_le continuous_const (hd i))
  have hKclosed : IsClosed K :=
    (isClosed_eq (contDiff_stateConstraint 1).continuous continuous_const).inter (hKw.inter hKd)
  have hK : IsCompact K := (isCompact_closedBall (0 : NormalizedState) 4).of_isClosed_subset hKclosed (by
    intro x hx
    have hb := normalizedState_norm_bound_abs hx.1 (fun i =>
      (abs_of_nonneg (hx.2.1 i).1).trans_le (hx.2.1 i).2)
    simpa only [Metric.mem_closedBall, dist_zero_right, mul_one, show (1 : ℝ) + 3 = 4 by norm_num] using hb)
  let F : NormalizedState → ℝ := fun x => max (wallGrowthMargin x) (x 2 + x 3 + x 4)
  have hF : Continuous F := continuous_wallGrowthMargin.max (by fun_prop)
  have hFpos (x : NormalizedState) (hx : x ∈ K) : 0 < F x := by
    have h2 : 0 ≤ x 2 := (hx.2.1 0).1
    have h3 : 0 ≤ x 3 := (hx.2.1 1).1
    have h4 : 0 ≤ x 4 := (hx.2.1 2).1
    by_cases hh : 0 < x 2 + x 3 + x 4
    · exact lt_max_of_lt_right hh
    · have hz2 : x 2 = 0 := by linarith only [h2, h3, h4, not_lt.mp hh]
      have hz3 : x 3 = 0 := by linarith only [h2, h3, h4, not_lt.mp hh]
      have hz4 : x 4 = 0 := by linarith only [h2, h3, h4, not_lt.mp hh]
      apply lt_max_of_lt_left
      apply normalized_kasner_growth_margin_pos hx.1 hz2 hz3 hz4
      intro i heq
      have hd := hx.2.2 i
      rw [heq] at hd
      have hz : normalizedEuclideanDistance (taubPoint i) (taubPoint i) = 0 := dist_self _
      rw [hz] at hd
      exact (not_le_of_gt hε) hd
  obtain ⟨d, hd, H⟩ := hK.exists_forall_le' hF.continuousOn hFpos
  let ν := min (1 / 4) (d / 6)
  let c := min 1 d
  have hν : 0 < ν := lt_min (by norm_num) (by positivity)
  refine ⟨ν, hν, min_le_left _ _, c, lt_min zero_lt_one hd, min_le_left _ _, ?_⟩
  intro x hc hw ha
  have hx : x ∈ K := ⟨hc, fun i => ⟨(hw i).1,
    (hw i).2.trans ((min_le_left _ _).trans (by norm_num : (1 / 4 : ℝ) ≤ 1))⟩, ha⟩
  have hs : x 2 + x 3 + x 4 ≤ d / 2 := by
    have h2 : x 2 ≤ ν := (hw 0).2
    have h3 : x 3 ≤ ν := (hw 1).2
    have h4 : x 4 ≤ ν := (hw 2).2
    have hνd : ν ≤ d / 6 := min_le_right _ _
    linarith only [h2, h3, h4, hνd]
  have hm : d ≤ wallGrowthMargin x := by
    rcases le_max_iff.mp (H x hx) with hh | hh
    · exact hh
    · linarith only [hh, hs, hd]
  exact exists_wall_rate_margin_of_le ((min_le_right _ _).trans hm)
