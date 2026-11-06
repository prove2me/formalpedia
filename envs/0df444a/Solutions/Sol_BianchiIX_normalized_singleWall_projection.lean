-- Prove2me | solution 1 for BianchiIX.normalized_singleWall_projection
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T04:05:54.837232+00:00
-- url     : https://prove2.me/submissions/58eb4c4c-ed61-46f5-a8fd-dbaa9481e38c

import Definitions.Def_BianchiIX_GeometricExceptionData
import Definitions.Def_BianchiIX_AxisAndOrbitData
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
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
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

noncomputable section
open BianchiIX

section
noncomputable section
open BianchiIX

private theorem BianchiIX.weak_wall_sum_of_products {n b c Δ ν : ℝ}
    (hν : 0 < ν) (hn : ν ≤ n) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hΔ : 0 ≤ Δ ∧ Δ ≤ ν / 8)
    (hnb : 4 * n * b ≤ Δ ^ 2) (hcn : 4 * c * n ≤ Δ ^ 2) :
    b + c ≤ Δ ^ 2 / (2 * n) ∧ b + c ≤ ν / 128 := by
  have hnpos : 0 < n := hν.trans_le hn
  have hsum : 2 * n * (b + c) ≤ Δ ^ 2 := by nlinarith only [hnb, hcn]
  have hΔsq : Δ ^ 2 ≤ ν ^ 2 / 64 := by nlinarith only [hΔ.1, hΔ.2, hν]
  have hνsum := mul_le_mul_of_nonneg_right hn (add_nonneg hb hc)
  refine ⟨(le_div_iff₀ (by positivity : 0 < 2 * n)).mpr (by nlinarith only [hsum]), ?_⟩
  nlinarith only [hsum, hΔsq, hνsum, hν]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.singleWall_shear_defect {p s n b c Δ : ℝ}
    (hc : constraint p s n b c = 1) (hn : 0 < n) (hnmax : n ≤ 1 / 4)
    (hb : 0 ≤ b) (hc' : 0 ≤ c) (hΔ : 0 ≤ Δ ∧ Δ ≤ n / 8)
    (hnb : 4 * n * b ≤ Δ ^ 2) (hcn : 4 * c * n ≤ Δ ^ 2) :
    0 ≤ shearSq p s - (1 - n ^ 2) ∧
      shearSq p s - (1 - n ^ 2) ≤ Δ ^ 2 ∧
      15 / 16 ≤ shearSq p s ∧ shearSq p s ≤ 2 := by
  have hw := (weak_wall_sum_of_products hn le_rfl hb hc' hΔ hnb hcn).2
  have hsum : 2 * n * (b + c) ≤ Δ ^ 2 := by nlinarith only [hnb, hcn]
  have hsmall : b + c ≤ 2 * n := by linarith only [hw, hn]
  have hprod := mul_le_mul_of_nonneg_left hsmall (add_nonneg hb hc')
  have hdiff : (b - c) ^ 2 ≤ (b + c) ^ 2 := by nlinarith only [mul_nonneg hb hc']
  have heq : shearSq p s - (1 - n ^ 2) = 2 * n * (b + c) - (b - c) ^ 2 := by
    dsimp [constraint, curvature] at hc
    nlinarith only [hc]
  have hlo : 0 ≤ shearSq p s - (1 - n ^ 2) := by
    nlinarith only [heq, hprod, hdiff]
  have hhi : shearSq p s - (1 - n ^ 2) ≤ Δ ^ 2 := by
    nlinarith only [heq, hsum, sq_nonneg (b - c)]
  have hnsq : n ^ 2 ≤ 1 / 16 := by nlinarith only [hn, hnmax]
  have hΔsq : Δ ^ 2 ≤ 1 := by nlinarith only [hΔ.1, hΔ.2, hnmax]
  exact ⟨hlo, hhi, by linarith only [hlo, hnsq],
    by linarith only [hhi, hΔsq, sq_nonneg n]⟩

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.singleWall_projection_scale_bounds {p s n b c Δ : ℝ}
    (hc : constraint p s n b c = 1) (hn : 0 < n) (hnmax : n ≤ 1 / 4)
    (hb : 0 ≤ b) (hc' : 0 ≤ c) (hΔ : 0 ≤ Δ ∧ Δ ≤ n / 8)
    (hnb : 4 * n * b ≤ Δ ^ 2) (hcn : 4 * c * n ≤ Δ ^ 2) :
    0 ≤ singleWallProjectionScale p s n ∧ singleWallProjectionScale p s n ≤ 1 ∧
      shearSq (singleWallProjectionScale p s n * p) (singleWallProjectionScale p s n * s) =
        1 - n ^ 2 ∧ 1 - singleWallProjectionScale p s n ≤ 2 * Δ ^ 2 := by
  obtain ⟨hlo, hhi, hq, _⟩ := singleWall_shear_defect hc hn hnmax hb hc' hΔ hnb hcn
  let q := shearSq p s
  let l := singleWallProjectionScale p s n
  have hqpos : 0 < q := by dsimp [q]; linarith only [hq]
  have hrad : 0 ≤ 1 - n ^ 2 := by nlinarith only [hn, hnmax]
  have hl0 : 0 ≤ l := Real.sqrt_nonneg _
  have hlsq : l ^ 2 * q = 1 - n ^ 2 := by
    dsimp [l, singleWallProjectionScale]
    rw [Real.sq_sqrt (div_nonneg hrad hqpos.le), div_mul_cancel₀ _ hqpos.ne']
  have hl1 : l ≤ 1 := by
    have H : l ^ 2 ≤ 1 := by nlinarith only [hlsq, hlo, hqpos]
    nlinarith only [H, hl0]
  have hlsql : l ^ 2 ≤ l := by nlinarith only [hl0, hl1]
  have H := mul_le_mul_of_nonneg_left hlsql hqpos.le
  have H' := mul_le_mul_of_nonneg_right (show 1 / 2 ≤ q by dsimp [q]; linarith only [hq])
    (sub_nonneg.mpr hl1)
  refine ⟨hl0, hl1, ?_, ?_⟩
  · change shearSq (l * p) (l * s) = 1 - n ^ 2
    calc
      _ = l ^ 2 * q := by dsimp [shearSq, q]; ring
      _ = _ := hlsq
  · change 1 - l ≤ 2 * Δ ^ 2
    change q - (1 - n ^ 2) ≤ Δ ^ 2 at hhi
    nlinarith only [H, H', hlsq, hhi]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.singleWall_projection_errors {p s n b c Δ : ℝ}
    (hc : constraint p s n b c = 1) (hn : 0 < n) (hnmax : n ≤ 1 / 4)
    (hb : 0 ≤ b) (hc' : 0 ≤ c) (hΔ : 0 ≤ Δ ∧ Δ ≤ n / 8)
    (hnb : 4 * n * b ≤ Δ ^ 2) (hcn : 4 * c * n ≤ Δ ^ 2) :
    |singleWallProjectionScale p s n * p - p| ≤ 4 * Δ ^ 2 ∧
      |singleWallProjectionScale p s n * s - s| ≤ 4 * Δ ^ 2 ∧
      |rateOne (singleWallProjectionScale p s n * p) (singleWallProjectionScale p s n * s) -
        rateOne p s| ≤ 9 * Δ ^ 2 := by
  obtain ⟨hlo, hhi, _, hq⟩ := singleWall_shear_defect hc hn hnmax hb hc' hΔ hnb hcn
  obtain ⟨hl0, hl1, hrad, hl⟩ := singleWall_projection_scale_bounds hc hn hnmax hb hc' hΔ hnb hcn
  let l := singleWallProjectionScale p s n
  have hp : |p| ≤ 2 := by
    dsimp [shearSq] at hq
    exact abs_le.mpr ⟨by nlinarith only [hq, sq_nonneg s], by nlinarith only [hq, sq_nonneg s]⟩
  have hs : |s| ≤ 2 := by
    dsimp [shearSq] at hq
    exact abs_le.mpr ⟨by nlinarith only [hq, sq_nonneg p], by nlinarith only [hq, sq_nonneg p]⟩
  have herr (z : ℝ) (hz : |z| ≤ 2) : |l * z - z| ≤ 4 * Δ ^ 2 := by
    rw [show l * z - z = -(1 - l) * z by ring, abs_mul, abs_neg,
      abs_of_nonneg (sub_nonneg.mpr hl1)]
    nlinarith only [mul_le_mul_of_nonneg_left hz (sub_nonneg.mpr hl1), hl]
  have hep := herr p hp
  have hes := herr s hs
  refine ⟨hep, hes, ?_⟩
  change |rateOne (l * p) (l * s) - rateOne p s| ≤ 9 * Δ ^ 2
  have heq : rateOne (l * p) (l * s) - rateOne p s =
      (shearSq p s - (1 - n ^ 2)) + 2 * (l * p - p) := by
    dsimp [rateOne]
    rw [hrad]
    ring
  rw [heq]
  calc
    _ ≤ |shearSq p s - (1 - n ^ 2)| + |2 * (l * p - p)| := abs_add_le _ _
    _ ≤ 9 * Δ ^ 2 := by rw [abs_of_nonneg hlo, abs_mul]; norm_num; linarith only [hhi, hep]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.normalizedEuclideanDistance_nonneg (x y : NormalizedState) :
    0 ≤ normalizedEuclideanDistance x y := dist_nonneg

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.normalizedEuclideanDistance_sq (x y : NormalizedState) :
    normalizedEuclideanDistance x y ^ 2 = ∑ i, (x i - y i) ^ 2 := by
  simp [normalizedEuclideanDistance, EuclideanSpace.dist_sq_eq, Real.dist_eq]

end
end


/-- Constraint-preserving projection with both the analytic and physical distance bounds. -/
theorem solution {x : NormalizedState} {Δ : ℝ}
    (hc : stateConstraint x = 1) (hp : positiveWalls x)
    (hnmax : x 2 ≤ 1 / 4) (hΔ : 0 ≤ Δ ∧ Δ ≤ x 2 / 8)
    (hprod : normalizedWallProductsBound Δ x) :
    stateConstraint (singleWallProjection x) = 1 ∧
      singleWallProjection x 2 = x 2 ∧ singleWallProjection x 3 = 0 ∧
      singleWallProjection x 4 = 0 ∧
      ‖singleWallProjection x - x‖ ≤ Δ ^ 2 / x 2 ∧
      normalizedEuclideanDistance (singleWallProjection x) x ≤ 2 * Δ ^ 2 / x 2 ∧
      |rateOne (singleWallProjection x 0) (singleWallProjection x 1) - rateOne (x 0) (x 1)| ≤
        9 * Δ ^ 2 := by
  have hscale := singleWall_projection_scale_bounds hc hp.1 hnmax hp.2.1.le hp.2.2.le hΔ hprod.1 hprod.2.2
  obtain ⟨hep, hes, her⟩ := singleWall_projection_errors hc hp.1 hnmax hp.2.1.le hp.2.2.le hΔ hprod.1 hprod.2.2
  have hweak := (weak_wall_sum_of_products hp.1 le_rfl hp.2.1.le hp.2.2.le hΔ hprod.1 hprod.2.2).1
  let E := Δ ^ 2 / x 2
  have hE : 0 ≤ E := div_nonneg (sq_nonneg Δ) hp.1.le
  have hshear : 4 * Δ ^ 2 ≤ E := by
    apply (le_div_iff₀ hp.1).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hnmax (sq_nonneg Δ)]
  have hweak' : x 3 + x 4 ≤ E / 2 := by
    convert hweak using 1
    dsimp [E]
    ring
  have hcoords (i : Fin 5) : |singleWallProjection x i - x i| ≤ E := by
    fin_cases i
    · exact hep.trans hshear
    · exact hes.trans hshear
    · simpa [singleWallProjection] using hE
    · simpa [singleWallProjection, abs_of_pos hp.2.1] using
        (show x 3 ≤ E by linarith only [hweak', hp.2.2, hE])
    · simpa [singleWallProjection, abs_of_pos hp.2.2] using
        (show x 4 ≤ E by linarith only [hweak', hp.2.1, hE])
  refine ⟨?_, rfl, rfl, rfl, ?_, ?_, her⟩
  · change shearSq _ _ + curvature (x 2) 0 0 = 1
    dsimp [singleWallProjection]
    rw [hscale.2.2.1]
    dsimp [curvature]
    ring
  · exact (pi_norm_le_iff_of_nonneg hE).mpr (fun i => by simpa only [Pi.sub_apply, Real.norm_eq_abs] using hcoords i)
  · have H (i : Fin 5) : (singleWallProjection x i - x i) ^ 2 ≤ E ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hE).mpr (hcoords i)
    have Hd := normalizedEuclideanDistance_sq (singleWallProjection x) x
    simp [Fin.sum_univ_succ, singleWallProjection] at Hd
    change normalizedEuclideanDistance (singleWallProjection x) x ^ 2 = _ at Hd
    have h0 := H 0
    have h1 := H 1
    have h3 := H 3
    have h4 := H 4
    dsimp [singleWallProjection] at h0 h1 h3 h4
    have Hsum : normalizedEuclideanDistance (singleWallProjection x) x ^ 2 ≤ 4 * E ^ 2 := by
      nlinarith only [Hd, h0, h1, h3, h4]
    have Hdist : normalizedEuclideanDistance (singleWallProjection x) x ≤ 2 * E := by
      nlinarith only [Hsum, hE, normalizedEuclideanDistance_nonneg (singleWallProjection x) x]
    convert Hdist using 1
    dsimp [E]
    ring
