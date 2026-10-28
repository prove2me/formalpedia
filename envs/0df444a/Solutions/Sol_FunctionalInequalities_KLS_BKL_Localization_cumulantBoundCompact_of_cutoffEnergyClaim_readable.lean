-- Prove2me | solution 1 for FunctionalInequalities.KLS.BKL.Localization.cumulantBoundCompact_of_cutoffEnergyClaim_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:24:42.544567+00:00
-- url     : https://prove2.me/submissions/d5bcd37e-42fd-4022-bf37-463853fc2c2d

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Operator_Coordinates
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Operator_InverseSqrt
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Cutoff_LipschitzBall
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Coefficients
import Definitions.Def_KLSModular_LevyStochCalc_Probability_Augmentation
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_AugmentedFiltration
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Diffusion_Setup
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Diffusion_Existence
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_CumulantEnvelope
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_CutoffEnergy_ToCumulant
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_exists_isEldanCutoff_readable
import Theorems.Thm_LevyStochCalc_Brownian_IsBrownianFiltration_rightCont_readable
import Theorems.Thm_LevyStochCalc_Brownian_Multidim_MultidimBrownianMotion_exists_readable
import Theorems.Thm_LevyStochCalc_Brownian_Multidim_MultidimBrownianMotion_isBrownianFiltration_natural_readable

section
noncomputable section
open scoped RealInnerProductSpace MatrixOrder
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section OperatorMatrix
open Matrix
variable [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι] [DecidableEq ι]
@[simp] theorem FunctionalInequalities.Analysis.operatorMatrix_operatorOfMatrix (b : OrthonormalBasis ι ℝ E) (M : Matrix ι ι ℝ) :
    operatorMatrix b (operatorOfMatrix b M) = M := by
  exact (LinearMap.toMatrixOrthonormal b).apply_symm_apply M
@[simp] theorem FunctionalInequalities.Analysis.operatorOfMatrix_operatorMatrix (b : OrthonormalBasis ι ℝ E) (T : E →L[ℝ] E) :
    operatorOfMatrix b (operatorMatrix b T) = T := by
  exact congrArg (fun f : E →ₗ[ℝ] E => f.toContinuousLinearMap)
    ((LinearMap.toMatrixOrthonormal b).symm_apply_apply T.toLinearMap)
theorem FunctionalInequalities.Analysis.operatorMatrix_injective (b : OrthonormalBasis ι ℝ E) : Function.Injective (operatorMatrix b) := by
  intro S T h
  have := congrArg (operatorOfMatrix b) h
  simpa only [operatorOfMatrix_operatorMatrix] using this
@[simp] theorem FunctionalInequalities.Analysis.operatorMatrix_mul (b : OrthonormalBasis ι ℝ E) (S T : E →L[ℝ] E) :
    operatorMatrix b (S * T) = operatorMatrix b S * operatorMatrix b T := by
  exact map_mul (LinearMap.toMatrixOrthonormal b) S.toLinearMap T.toLinearMap
@[simp] theorem FunctionalInequalities.Analysis.operatorMatrix_one (b : OrthonormalBasis ι ℝ E) :
    operatorMatrix b (1 : E →L[ℝ] E) = 1 := by
  exact map_one (LinearMap.toMatrixOrthonormal b)
/-- The matrix is positive semidefinite iff the operator is positive (Mathlib `posSemidef_toMatrix_iff`). -/
theorem FunctionalInequalities.Analysis.operatorMatrix_posSemidef_iff (b : OrthonormalBasis ι ℝ E) (T : E →L[ℝ] E) :
    (operatorMatrix b T).PosSemidef ↔ T.IsPositive :=
  LinearMap.posSemidef_toMatrix_iff b
/-- The matrix inverse of a unit's matrix is the matrix of `Ring.inverse`. -/
theorem FunctionalInequalities.Analysis.operatorMatrix_ringInverse (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E) (hA : IsUnit A) :
    (operatorMatrix b A)⁻¹ = operatorMatrix b (Ring.inverse A) := by
  apply Matrix.inv_eq_right_inv
  rw [← operatorMatrix_mul, Ring.mul_inverse_cancel A hA, operatorMatrix_one]
end OperatorMatrix
end
end
end

section
noncomputable section
open scoped MatrixOrder RealInnerProductSpace
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
@[simp] theorem FunctionalInequalities.Analysis.operatorMatrix_inverseSqrtIn (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E) :
    operatorMatrix b (inverseSqrtIn b A) = CFC.sqrt ((operatorMatrix b A)⁻¹) :=
  operatorMatrix_operatorOfMatrix b _
/-- Uniqueness of the positive branch: any positive `S` with `S² = A⁻¹` equals `inverseSqrtIn b A`. -/
theorem FunctionalInequalities.Analysis.inverseSqrtIn_unique (b : OrthonormalBasis ι ℝ E) (A S : E →L[ℝ] E)
    (hunit : IsUnit A) (hS : S.IsPositive) (hSquare : S * S = Ring.inverse A) :
    inverseSqrtIn b A = S := by
  apply operatorMatrix_injective b
  rw [operatorMatrix_inverseSqrtIn]
  apply CFC.sqrt_unique
  · rw [← operatorMatrix_mul, hSquare, operatorMatrix_ringInverse b A hunit]
  · exact ((operatorMatrix_posSemidef_iff b S).mpr hS).nonneg
theorem FunctionalInequalities.Analysis.inverseSqrt_unique (A S : E →L[ℝ] E)
    (hunit : IsUnit A) (hS : S.IsPositive) (hSquare : S * S = Ring.inverse A) :
    inverseSqrt A = S := inverseSqrtIn_unique _ A S hunit hS hSquare
end
end
end

section
noncomputable section
open scoped NNReal
section Cutoff
variable {V V' : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup V'] [NormedSpace ℝ V']
theorem FunctionalInequalities.Probability.Diffusion.ballCutoff_mem_Icc (R : ℝ) (p : V) : ballCutoff R p ∈ Set.Icc (0 : ℝ) 1 := by
  have _hcompact := isCompact_closedBall (0 : V) (1 : ℝ)
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
theorem FunctionalInequalities.Probability.Diffusion.lipschitzWith_ballCutoff (R : ℝ) : LipschitzWith 1 (ballCutoff (V := V) R) := by
  have _hcompact := isCompact_closedBall (0 : V) (1 : ℝ)
  have hn : LipschitzWith 1 (fun x : V => ‖x‖) :=
    LipschitzWith.of_dist_le_mul fun x y => by
      simpa only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_one, one_mul] using
        abs_norm_sub_norm_le x y
  change LipschitzWith 1 (fun p : V => max 0 (min 1 (R + 1 - ‖p‖)))
  simpa only [zero_add, max_eq_right (show (0 : ℝ≥0) ≤ 1 by positivity)] using
    (LipschitzWith.const (0 : ℝ)).max
      ((LipschitzWith.const (1 : ℝ)).min ((LipschitzWith.const (R + 1)).sub hn))
theorem FunctionalInequalities.Probability.Diffusion.hasCompactSupport_ballCutoff (R : ℝ) : HasCompactSupport (ballCutoff (V := V) R) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : V) (R + 1))
  intro x hx
  have hr : R + 1 ≤ ‖x‖ :=
    le_of_lt (lt_of_not_ge (by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hx))
  exact max_eq_left (le_trans (min_le_right _ _) (sub_nonpos.mpr hr))
end Cutoff
end
end

section
noncomputable section
open MeasureTheory
open scoped NNReal RealInnerProductSpace
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Probability.Diffusion
section
variable {n : ℕ} (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support)
theorem FunctionalInequalities.KLS.BKL.Localization.isCutoff_ballCutoff (R : ℝ) : IsCutoff (ballCutoff (V := Param n) R) :=
  { lipschitz := ⟨1, lipschitzWith_ballCutoff R⟩
    compactSupport := hasCompactSupport_ballCutoff R
    mem_Icc := fun p => ballCutoff_mem_Icc R p }
end
end
end

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Probability/Augmentation.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory
open scoped symmDiff
section
variable {Ω : Type*}
variable {m m₀ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω}
theorem LevyStochCalc.Probability.le_aug (hm : m ≤ m₀) : m ≤ aug m m₀ μ := fun A hA =>
  ⟨hm A hA, A, hA, by simp⟩
/-- Null sets are augmented-measurable. -/
theorem LevyStochCalc.Probability.measurableSet_aug_of_null {A : Set Ω} (hA : MeasurableSet[m₀] A)
    (h : μ A = 0) : MeasurableSet[aug m m₀ μ] A :=
  ⟨hA, ∅, @MeasurableSet.empty Ω m, by simpa using h⟩
end
end

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/AugmentedFiltration.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
section
/-- **Independence survives augmentation by the null sets.** -/
theorem LevyStochCalc.Probability.indep_aug {Ω : Type*} {mΩ m 𝒩 : MeasurableSpace Ω} (μ : @Measure Ω mΩ)
    (h : @Indep Ω m 𝒩 mΩ μ) : @Indep Ω (aug m mΩ μ) 𝒩 mΩ μ := by
  rw [Indep_iff] at h ⊢
  rintro A C ⟨-, B, hB, hAB⟩ hC
  have hae : A =ᵐ[μ] B := MeasureTheory.measure_symmDiff_eq_zero_iff.mp hAB
  have h1 : μ A = μ B := MeasureTheory.measure_congr hae
  have h2 : μ (A ∩ C) = μ (B ∩ C) :=
    MeasureTheory.measure_congr (hae.inter (Filter.EventuallyEq.refl _ _))
  rw [h1, h2]
  exact h B C hB hC
end
section
open LevyStochCalc.Probability
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
theorem LevyStochCalc.Brownian.le_augFiltration (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (μ : Measure Ω) (t : ℝ) :
    ℱ t ≤ augFiltration ℱ μ t :=
  le_trans (ℱ.mono (le_max_left t 0)) (le_aug (ℱ.le _))
theorem LevyStochCalc.Brownian.measurableSet_augFiltration_of_null (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (μ : Measure Ω) {s : Set Ω} (hs : MeasurableSet s) (h0 : μ s = 0) :
    MeasurableSet[augFiltration ℱ μ 0] s :=
  measurableSet_aug_of_null hs h0
/-- **The `0`-clamped augmented filtration is a Brownian filtration.** -/
theorem LevyStochCalc.Brownian.isBrownianFiltration_augFiltration {W : BrownianMotion P}
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (h : IsBrownianFiltration W ℱ) :
    IsBrownianFiltration W (augFiltration ℱ P) where
  measurable t := fun A hA => le_augFiltration ℱ P t _ (h.measurable t hA)
  indep_future s hs := by
    have hfeq : (augFiltration ℱ P) s = aug (ℱ s) ‹MeasurableSpace Ω› P := by
      change aug (ℱ (max s 0)) ‹MeasurableSpace Ω› P = aug (ℱ s) ‹MeasurableSpace Ω› P
      rw [max_eq_left hs]
    rw [hfeq]
    exact indep_aug P (h.indep_future hs)
end
end

section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
section
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
  LevyStochCalc.Brownian.Ito
section Usual
variable {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] {d : ℕ}
theorem FunctionalInequalities.Probability.Diffusion.usualFiltration_brownian (W : MultidimBrownianMotion P d) (k : Fin d) :
    IsBrownianFiltration (W.W k) (usualFiltration W) :=
  isBrownianFiltration_augFiltration (W.isBrownianFiltration_natural_readable k).rightCont_readable
theorem FunctionalInequalities.Probability.Diffusion.usualFiltration_le_of_nonpos (W : MultidimBrownianMotion P d) (t : ℝ) (ht : t ≤ 0) :
    usualFiltration W 0 ≤ usualFiltration W t :=
  le_of_eq (augFiltration_of_nonpos W.naturalFiltration.rightCont P ht).symm
theorem FunctionalInequalities.Probability.Diffusion.usualFiltration_null (W : MultidimBrownianMotion P d) (s : Set Ω)
    (hs : MeasurableSet s) (h0 : P s = 0) : MeasurableSet[usualFiltration W 0] s :=
  measurableSet_augFiltration_of_null W.naturalFiltration.rightCont P hs h0
end Usual
end
end

section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
section
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
  LevyStochCalc.Brownian.Ito
universe u
section Diffusion
variable {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
  [MeasureTheory.IsProbabilityMeasure P] {N d : ℕ}
theorem FunctionalInequalities.Probability.Diffusion.exists_brownianSetup (d : ℕ) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (_ : MultidimBrownianMotion P d), True := by
  obtain ⟨Ω, _, P, _, ⟨W⟩⟩ := MultidimBrownianMotion.exists_readable.{0} d
  exact ⟨Ω, inferInstance, P, inferInstance, W, trivial⟩
end Diffusion
end
end

section
noncomputable section
section
theorem FunctionalInequalities.KLS.BKL.envelope_nonneg {K : ℝ} (hK : 0 ≤ K) (m : ℕ) : 0 ≤ envelope K m := by
  unfold envelope
  positivity
end
end
end

noncomputable section
section S7CClaimToBound
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Probability.Diffusion
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim LevyStochCalc.Brownian.Ito
/-- For an isotropic law the energy at the initial parameter is the standard-basis sum
`Σ_J κ_{d+1}(u, e_J)²` (`σ = Cov⁻¹ᐟ² = Id`). -/
theorem FunctionalInequalities.KLS.BKL.Localization.cumulantEnergy_eq_sum_sq_of_isotropic {n : ℕ} (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hiso : KLS.Isotropic μ) (d : ℕ) (u : EuclideanSpace ℝ (Fin n)) :
    cumulantEnergy (μ : Measure (EuclideanSpace ℝ (Fin n))) d u =
      ∑ J : Fin d → Fin n, cumulant (μ : Measure (EuclideanSpace ℝ (Fin n))) (d + 1)
        (Fin.cons u fun k => EuclideanSpace.basisFun (Fin n) ℝ (J k)) ^ 2 := by
  have hsqrt :
      inverseSqrt (Covariance.operator (μ : Measure (EuclideanSpace ℝ (Fin n)))) =
        ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
    rw [hiso.covariance_identity]
    change inverseSqrt (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) = 1
    apply inverseSqrt_unique _ _ isUnit_one
    · exact ContinuousLinearMap.isPositive_one
    · simp
  simp only [cumulantEnergy, hsqrt, ContinuousLinearMap.id_apply]
/-- **From the cutoff claim to the cumulant bound** (BKL p. 27, `E_m(0) = ⟨R^μ_m u, u⟩`): `CutoffEnergyClaim K d`
gives `CumulantBoundCompact d (envelope K (d + 1))`. -/
theorem solution {K : ℝ} (hK : 0 ≤ K) {d : ℕ} (h : FunctionalInequalities.KLS.BKL.Localization.CutoffEnergyClaim K d) :
    FunctionalInequalities.KLS.LogConcave.Suspension.CumulantBoundCompact d (FunctionalInequalities.KLS.BKL.envelope K (d + 1)) := by
  classical
  unfold FunctionalInequalities.KLS.LogConcave.Suspension.CumulantBoundCompact
  intro m ν hiso hLC hc u
  by_cases hu0 : u = 0
  · subst u
    have hzero (J : Fin d → Fin m) :
        FunctionalInequalities.Analysis.BakryEmery.cumulant (ν : Measure (EuclideanSpace ℝ (Fin m))) (d + 1)
            (Fin.cons (0 : EuclideanSpace ℝ (Fin m))
              (fun k => EuclideanSpace.basisFun (Fin m) ℝ (J k))) = 0 := by
      exact
        (FunctionalInequalities.Analysis.BakryEmery.cumulant (ν : Measure (EuclideanSpace ℝ (Fin m))) (d + 1)).map_coord_zero 0
          (by simp)
    calc
      ∑ J : Fin d → Fin m,
          FunctionalInequalities.Analysis.BakryEmery.cumulant (ν : Measure (EuclideanSpace ℝ (Fin m))) (d + 1)
            (Fin.cons (0 : EuclideanSpace ℝ (Fin m))
              (fun k => EuclideanSpace.basisFun (Fin m) ℝ (J k))) ^ 2 = 0 := by
        apply Finset.sum_eq_zero
        intro J _
        rw [hzero J]
        norm_num
      _ ≤ FunctionalInequalities.KLS.BKL.envelope K (d + 1) * ‖(0 : EuclideanSpace ℝ (Fin m))‖ ^ 2 :=
        mul_nonneg (FunctionalInequalities.KLS.BKL.envelope_nonneg hK (d + 1)) (sq_nonneg _)
  · let v : EuclideanSpace ℝ (Fin m) := ‖u‖⁻¹ • u
    have hnorm : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu0
    have hv : ‖v‖ = 1 := by
      calc
        ‖v‖ = ‖(‖u‖ : ℝ)⁻¹‖ * ‖u‖ := norm_smul _ _
        _ = ‖u‖⁻¹ * ‖u‖ := by
          rw [Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg u)]
        _ = 1 := inv_mul_cancel₀ hnorm
    have huv : ‖u‖ • v = u := by
      dsimp [v]
      rw [smul_smul, mul_inv_cancel₀ hnorm, one_smul]
    have hunitApprox (ε : ℝ) (hε : 0 < ε) :
        ∑ J : Fin d → Fin m,
            FunctionalInequalities.Analysis.BakryEmery.cumulant (ν : Measure (EuclideanSpace ℝ (Fin m))) (d + 1)
              (Fin.cons v
                (fun k => EuclideanSpace.basisFun (Fin m) ℝ (J k))) ^ 2
          ≤ FunctionalInequalities.KLS.BKL.envelope K (d + 1) + ε := by
      obtain ⟨Ω, _, P, _, W, _⟩ :=
        FunctionalInequalities.Probability.Diffusion.exists_brownianSetup m
      let ℱ : Filtration ℝ ‹MeasurableSpace Ω› := FunctionalInequalities.Probability.Diffusion.usualFiltration W
      have hright : ℱ.IsRightContinuous := by
        dsimp [ℱ]
        infer_instance
      have hW : ∀ k, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ := by
        intro k
        change LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) (FunctionalInequalities.Probability.Diffusion.usualFiltration W)
        exact FunctionalInequalities.Probability.Diffusion.usualFiltration_brownian W k
      have hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t := by
        intro t ht
        change FunctionalInequalities.Probability.Diffusion.usualFiltration W 0 ≤ FunctionalInequalities.Probability.Diffusion.usualFiltration W t
        exact FunctionalInequalities.Probability.Diffusion.usualFiltration_le_of_nonpos W t ht
      have hnull :
          ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s := by
        intro s hs hPs
        change MeasurableSet[FunctionalInequalities.Probability.Diffusion.usualFiltration W 0] s
        exact FunctionalInequalities.Probability.Diffusion.usualFiltration_null W s hs hPs
      obtain ⟨R₀, hR₀⟩ := h m ν hc hiso hLC v hv ε hε 0 (by norm_num)
      obtain ⟨p, hp⟩ :=
        @FunctionalInequalities.KLS.BKL.Localization.exists_isEldanCutoff_readable m ν hc hiso Ω _ P _ W ℱ hright hW hℱ0 hnull
          (FunctionalInequalities.Probability.Diffusion.ballCutoff R₀) (FunctionalInequalities.KLS.BKL.Localization.isCutoff_ballCutoff R₀)
      have hineq := hR₀ R₀ le_rfl W ℱ hW hℱ0 hnull hp
      have hzeroIntegral :
          FunctionalInequalities.KLS.BKL.Localization.weightedEnergyIntegral ν hc P (FunctionalInequalities.Probability.Diffusion.ballCutoff R₀) p (d + 1) v 0 = 0 := by
        simp [FunctionalInequalities.KLS.BKL.Localization.weightedEnergyIntegral]
      rw [hzeroIntegral, mul_zero, add_zero] at hineq
      calc
        ∑ J : Fin d → Fin m,
            FunctionalInequalities.Analysis.BakryEmery.cumulant (ν : Measure (EuclideanSpace ℝ (Fin m))) (d + 1)
              (Fin.cons v
                (fun k => EuclideanSpace.basisFun (Fin m) ℝ (J k))) ^ 2
            =
            FunctionalInequalities.KLS.BKL.cumulantEnergy (ν : Measure (EuclideanSpace ℝ (Fin m))) d v :=
              (FunctionalInequalities.KLS.BKL.Localization.cumulantEnergy_eq_sum_sq_of_isotropic ν hiso d v).symm
        _ ≤ FunctionalInequalities.KLS.BKL.envelope K (d + 1) + ε := hineq
    have hunit :
        ∑ J : Fin d → Fin m,
            FunctionalInequalities.Analysis.BakryEmery.cumulant (ν : Measure (EuclideanSpace ℝ (Fin m))) (d + 1)
              (Fin.cons v
                (fun k => EuclideanSpace.basisFun (Fin m) ℝ (J k))) ^ 2
          ≤ FunctionalInequalities.KLS.BKL.envelope K (d + 1) := by
      apply le_of_forall_pos_lt_add
      intro ε hε
      have hhalf := hunitApprox (ε / 2) (by linarith)
      linarith
    have hscale (J : Fin d → Fin m) :
        FunctionalInequalities.Analysis.BakryEmery.cumulant (ν : Measure (EuclideanSpace ℝ (Fin m))) (d + 1)
            (Fin.cons u
              (fun k => EuclideanSpace.basisFun (Fin m) ℝ (J k))) =
          ‖u‖ *
            FunctionalInequalities.Analysis.BakryEmery.cumulant (ν : Measure (EuclideanSpace ℝ (Fin m))) (d + 1)
              (Fin.cons v
                (fun k => EuclideanSpace.basisFun (Fin m) ℝ (J k))) := by
      calc
        FunctionalInequalities.Analysis.BakryEmery.cumulant (ν : Measure (EuclideanSpace ℝ (Fin m))) (d + 1)
            (Fin.cons u
              (fun k => EuclideanSpace.basisFun (Fin m) ℝ (J k))) =
            FunctionalInequalities.Analysis.BakryEmery.cumulant (ν : Measure (EuclideanSpace ℝ (Fin m))) (d + 1)
              (Function.update
                (Fin.cons v
                  (fun k => EuclideanSpace.basisFun (Fin m) ℝ (J k))) 0
                (‖u‖ • v)) := by
                  rw [Fin.update_cons_zero, huv]
        _ =
            ‖u‖ •
              FunctionalInequalities.Analysis.BakryEmery.cumulant (ν : Measure (EuclideanSpace ℝ (Fin m))) (d + 1)
                (Function.update
                  (Fin.cons v
                    (fun k => EuclideanSpace.basisFun (Fin m) ℝ (J k))) 0 v) :=
              (FunctionalInequalities.Analysis.BakryEmery.cumulant (ν : Measure (EuclideanSpace ℝ (Fin m))) (d + 1)).map_update_smul
                (Fin.cons v
                  (fun k => EuclideanSpace.basisFun (Fin m) ℝ (J k))) 0 ‖u‖ v
        _ =
            ‖u‖ *
              FunctionalInequalities.Analysis.BakryEmery.cumulant (ν : Measure (EuclideanSpace ℝ (Fin m))) (d + 1)
                (Fin.cons v
                  (fun k => EuclideanSpace.basisFun (Fin m) ℝ (J k))) := by
              rw [Fin.update_cons_zero, smul_eq_mul]
    calc
      ∑ J : Fin d → Fin m,
          FunctionalInequalities.Analysis.BakryEmery.cumulant (ν : Measure (EuclideanSpace ℝ (Fin m))) (d + 1)
            (Fin.cons u
              (fun k => EuclideanSpace.basisFun (Fin m) ℝ (J k))) ^ 2 =
          ∑ J : Fin d → Fin m,
            ‖u‖ ^ 2 *
              FunctionalInequalities.Analysis.BakryEmery.cumulant (ν : Measure (EuclideanSpace ℝ (Fin m))) (d + 1)
                (Fin.cons v
                  (fun k => EuclideanSpace.basisFun (Fin m) ℝ (J k))) ^ 2 := by
            apply Finset.sum_congr rfl
            intro J _
            rw [hscale, mul_pow]
      _ =
          ‖u‖ ^ 2 *
            ∑ J : Fin d → Fin m,
              FunctionalInequalities.Analysis.BakryEmery.cumulant (ν : Measure (EuclideanSpace ℝ (Fin m))) (d + 1)
                (Fin.cons v
                  (fun k => EuclideanSpace.basisFun (Fin m) ℝ (J k))) ^ 2 := by
            rw [Finset.mul_sum]
      _ ≤ ‖u‖ ^ 2 * FunctionalInequalities.KLS.BKL.envelope K (d + 1) :=
        mul_le_mul_of_nonneg_left hunit (sq_nonneg ‖u‖)
      _ = FunctionalInequalities.KLS.BKL.envelope K (d + 1) * ‖u‖ ^ 2 := mul_comm _ _
