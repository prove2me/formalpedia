-- Prove2me | solution 1 for BianchiIX.exists_compactEraPhase_of_taub_avoidance
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T04:13:09.027209+00:00
-- url     : https://prove2.me/submissions/6951b2c0-cd34-46a2-af3c-fc6cce26bd65

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreEntryDifferential
import Definitions.Def_BianchiIX_AxisAndOrbitData
import Definitions.Def_BianchiIX_GeometricExceptionData
import Theorems.Thm_BianchiIX_exists_core_even_separation
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.List.Induction
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.Floor

noncomputable section
open BianchiIX

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

section
noncomputable section
open BianchiIX

private theorem BianchiIX.fromProjectiveState_taubDistance_sq {y : ProjectiveState}
    (hD : projectiveStateDenom y ≠ 0) :
    normalizedEuclideanDistance (fromProjectiveState y) (taubPoint 0) ^ 2 =
      12 * (3 + y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2) / projectiveStateDenom y ^ 2 := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  rw [normalizedEuclideanDistance_sq]
  simp [Fin.sum_univ_succ, fromProjectiveState, taubPoint]
  field_simp
  ring_nf
  simp only [hs]
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreRadiusEntry_taubDistance_bound {Y : CoreAngleState} (hk : 1 ≤ Y 0)
    (hu : 0 ≤ Y 1 ∧ Y 1 ≤ 1 / 100) (hw : 0 ≤ Y 2 ∧ Y 2 ≤ 1 / 100) :
    normalizedEuclideanDistance (fromProjectiveState (coreRadiusEntry Y)) (taubPoint 0) ^ 2 ≤
      48 / Y 0 ^ 2 := by
  let m := 1 + Real.sqrt (Y 0 ^ 2 - 1)
  let d₀ := 3 + m ^ 2 + Y 1 ^ 2 + 1 + Y 2 ^ 2
  let d := projectiveStateDenom (coreRadiusEntry Y)
  have hm : Y 0 ≤ m := by
    have H : Y 0 - 1 ≤ Real.sqrt (Y 0 ^ 2 - 1) := Real.le_sqrt_of_sq_le (by nlinarith only [hk])
    dsimp [m]
    linarith only [H]
  have hd₀ : 0 < d₀ := by dsimp [d₀]; positivity
  have hk₀ : 0 < Y 0 := lt_of_lt_of_le zero_lt_one hk
  have hkd : Y 0 ^ 2 ≤ d₀ := by
    have H := (sq_le_sq₀ hk₀.le (hk₀.le.trans hm)).mpr hm
    dsimp [d₀]
    nlinarith only [H, sq_nonneg (Y 1), sq_nonneg (Y 2)]
  have hproduct : Y 1 * Y 2 ≤ (1 / 100 : ℝ) ^ 2 := by
    simpa only [pow_two] using mul_le_mul hu.2 hw.2 hw.1 (by norm_num : (0 : ℝ) ≤ 1 / 100)
  have hhalf : d₀ / 2 ≤ d := by
    have hd : d = d₀ - 2 * (Y 1 + Y 1 * Y 2 + Y 2) := by
      dsimp [d, d₀, m, projectiveStateDenom, coreRadiusEntry, projectiveDenom, curvature]
      ring
    rw [hd]
    dsimp [d₀]
    nlinarith only [hu.2, hw.2, hproduct, sq_nonneg m, sq_nonneg (Y 1), sq_nonneg (Y 2)]
  have hd : 0 < d := lt_of_lt_of_le (half_pos hd₀) hhalf
  have hdist : normalizedEuclideanDistance (fromProjectiveState (coreRadiusEntry Y)) (taubPoint 0) ^ 2 =
      12 * d₀ / d ^ 2 := by
    convert fromProjectiveState_taubDistance_sq hd.ne' using 1
    simp [d₀, m, coreRadiusEntry, d]
  rw [hdist]
  have hfirst : 12 * d₀ / d ^ 2 ≤ 48 / d₀ := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hd) hd₀).mpr
    have H := (sq_le_sq₀ (half_pos hd₀).le hd.le).mpr hhalf
    nlinarith only [H]
  exact hfirst.trans (div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hk₀) hkd)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreRadiusEntry_radius_bound_of_away {Y : CoreAngleState} {ε : ℝ} (hε : 0 < ε)
    (hk : 1 ≤ Y 0) (hu : 0 ≤ Y 1 ∧ Y 1 ≤ 1 / 100) (hw : 0 ≤ Y 2 ∧ Y 2 ≤ 1 / 100)
    (haway : ε ≤ normalizedEuclideanDistance (fromProjectiveState (coreRadiusEntry Y)) (taubPoint 0)) :
    Y 0 < 8 / ε := by
  have hk₀ : 0 < Y 0 := lt_of_lt_of_le zero_lt_one hk
  have H := (le_div_iff₀ (sq_pos_of_pos hk₀)).mp (coreRadiusEntry_taubDistance_bound hk hu hw)
  have Hε := (sq_le_sq₀ hε.le (normalizedEuclideanDistance_nonneg _ _)).mpr haway
  have Hprod := mul_le_mul_of_nonneg_right Hε (sq_nonneg (Y 0))
  have Hsq : (ε * Y 0) ^ 2 ≤ 48 := by nlinarith only [H, Hprod]
  apply (lt_div_iff₀ hε).mpr
  nlinarith only [Hsq, mul_pos hε hk₀]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.normalizedTaubAvoidance.initial {ε : ℝ} {x : NormalizedState}
    (H : normalizedTaubAvoidance ε x) : ∀ i, ε ≤ normalizedEuclideanDistance x (taubPoint i) := by
  simpa only [normalizedMaxCurve_initial] using H 0 le_rfl (initial_mem_normalizedMaxDomain x 0)

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.mem_compactEraPhase_of_integer_separation {N : ℕ} {γ : ℝ} {X : CoreAngleState}
    (hγ : 0 ≤ γ) (hlo : 2 + 2 * γ ≤ X 0) (hhi : X 0 ≤ 2 * N)
    (hsep : ∀ k : ℤ, γ ≤ |X 0 / 2 - k|) : X ∈ compactEraPhase N γ := by
  have hx : 0 ≤ X 0 / 2 := by linarith only [hlo, hγ]
  have hf := Nat.floor_le hx
  have hnext := Nat.lt_floor_add_one (X 0 / 2)
  have hleft := hsep (⌊X 0 / 2⌋₊ : ℤ)
  have hright := hsep ((⌊X 0 / 2⌋₊ : ℤ) + 1)
  push_cast at hleft hright
  rw [abs_of_nonneg (sub_nonneg.mpr hf)] at hleft
  rw [abs_of_nonpos (by linarith only [hnext])] at hright
  exact ⟨hlo, hhi, hleft, by linarith only [hright]⟩

end
end


/-- Physical Taub avoidance forces every sufficiently small core into one common compact phase range. -/
theorem solution {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∃ γ > (0 : ℝ), γ < 1 / 4 ∧ ∃ B > (0 : ℝ),
      ∀ Y : CoreAngleState, 2 - γ / 2 ≤ Y 0 → 0 < Y 1 → 0 < Y 2 → Y 1 + Y 2 ≤ B →
        normalizedTaubAvoidance ε (fromProjectiveState (coreRadiusEntry Y)) →
        Y ∈ compactEraPhase N γ := by
  obtain ⟨δ, hδ, _, C, hC, H⟩ := exists_core_even_separation
  obtain ⟨ρ, hρ, hρmax, Hsep⟩ := H ε hε
  let K := 8 / ε
  let N := ⌈K / 2⌉₊
  let γ := ρ / 4
  let B := min (1 / 100) (min (δ / (1 + K)) (ρ / (4 * C)))
  have hK : 0 < K := div_pos (by norm_num) hε
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hB : 0 < B := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have hγmax : γ < 1 / 4 := by dsimp [γ]; linarith only [hρmax]
  refine ⟨N, γ, hγ, hγmax, B, hB, ?_⟩
  intro Y hk hu hw hb ha
  have hk1 : 1 ≤ Y 0 := by linarith only [hk, hγmax]
  have hb100 : Y 1 + Y 2 ≤ 1 / 100 := hb.trans (min_le_left _ _)
  have hu100 : 0 ≤ Y 1 ∧ Y 1 ≤ 1 / 100 := ⟨hu.le, by linarith only [hb100, hw]⟩
  have hw100 : 0 ≤ Y 2 ∧ Y 2 ≤ 1 / 100 := ⟨hw.le, by linarith only [hb100, hu]⟩
  have hupper : Y 0 < K := coreRadiusEntry_radius_bound_of_away hε hk1 hu100 hw100 (ha.initial 0)
  have hbudget : Y 1 + Y 2 ≤ δ / (1 + Y 0) :=
    (hb.trans ((min_le_right _ _).trans (min_le_left _ _))).trans
      (div_le_div_of_nonneg_left hδ.le (by linarith only [hk1]) (by linarith only [hupper]))
  have hsmall : C * (Y 1 + Y 2) ≤ ρ / 4 := by
    have HH : Y 1 + Y 2 ≤ ρ / (4 * C) := hb.trans ((min_le_right _ _).trans (min_le_right _ _))
    have HH' := (le_div_iff₀ (by positivity : 0 < 4 * C)).mp HH
    nlinarith only [HH']
  have hsep := Hsep Y hu hw hbudget hsmall ha
  have hlo : 2 + 2 * γ ≤ Y 0 := by
    have HH := hsep 1 (by omega)
    norm_num only [Nat.cast_one, mul_one] at HH
    rcases lt_abs.mp HH with hp | hm
    · dsimp [γ]
      linarith only [hp]
    · dsimp [γ] at hk
      linarith only [hm, hk, hρ]
  have hN : K / 2 ≤ (N : ℝ) := Nat.le_ceil _
  apply mem_compactEraPhase_of_integer_separation hγ.le hlo (by linarith only [hupper, hN])
  intro k
  cases k with
  | ofNat n =>
    rw [Int.ofNat_eq_natCast, Int.cast_natCast]
    cases n with
    | zero =>
      rw [Nat.cast_zero, sub_zero]
      rw [abs_of_nonneg (by linarith only [hlo, hγ] : 0 ≤ Y 0 / 2)]
      linarith only [hlo]
    | succ n =>
      have HH := hsep (n + 1) (by omega)
      have heq : Y 0 - 2 * (n + 1 : ℕ) = 2 * (Y 0 / 2 - (n + 1 : ℕ)) := by ring
      rw [heq, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at HH
      change γ ≤ |Y 0 / 2 - (n + 1 : ℕ)|
      dsimp [γ]
      exact (by linarith only [HH] : ρ / 4 ≤ |Y 0 / 2 - (n + 1 : ℕ)|)
  | negSucc n =>
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    simp only [Int.cast_negSucc, Nat.cast_add, Nat.cast_one]
    rw [abs_of_nonneg (by linarith only [hlo, hγ, hn] : 0 ≤ Y 0 / 2 - -((n : ℝ) + 1))]
    linarith only [hlo, hn]
