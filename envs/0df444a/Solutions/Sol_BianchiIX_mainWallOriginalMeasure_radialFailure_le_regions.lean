-- Prove2me | solution 1 for BianchiIX.mainWallOriginalMeasure_radialFailure_le_regions
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T04:08:49.253207+00:00
-- url     : https://prove2.me/submissions/18a7e1a7-578e-4ed8-8de4-1102fa946bc3

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_RadialFailureData
import Definitions.Def_BianchiIX_Algebra_Flux
import Definitions.Def_BianchiIX_AxisAndOrbitData
import Definitions.Def_BianchiIX_SectionRestartData
import Definitions.Def_BianchiIX_AxisSectionMeasureData
import Theorems.Thm_BianchiIX_restartRadialFailureSet_subset_regions
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
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Alternating.Curry
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.NormNum
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
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.MetricSpace.Thickening
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
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.List.Induction
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.OrderIsoNat
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Dynamics.BirkhoffSum.NormedSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

noncomputable section
open BianchiIX
open Set MeasureTheory

section
noncomputable section
open BianchiIX
open MeasureTheory
open scoped Topology ENNReal

private theorem BianchiIX.dyadicScale_pos {d : ℝ} (hd : 0 < d) (j : ℕ) : 0 < dyadicScale d j := by
  exact mul_pos hd (pow_pos (by norm_num) _)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.wallAmplitude_le_square {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hba : b ≤ a) (hca : c ≤ a) : wallAmplitude a b c ≤ a ^ 2 := by
  have hp : a * b * c ≤ a ^ 3 := by
    calc
      a * b * c ≤ a * a * a :=
        mul_le_mul (mul_le_mul_of_nonneg_left hba ha) hca hc (mul_nonneg ha ha)
      _ = a ^ 3 := by ring
  unfold wallAmplitude
  calc
    _ ≤ (a ^ 3) ^ (2 / 3 : ℝ) :=
      Real.rpow_le_rpow (mul_nonneg (mul_nonneg ha hb) hc) hp (by norm_num)
    _ = a ^ 2 := by rw [← Real.rpow_natCast_mul ha]; norm_num

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.measurable_mainWallChartDensity (h : ℝ) : Measurable (mainWallChartDensity h) := by
  unfold mainWallChartDensity correctedSectionFluxDensity sectionFluxDensity shearSq
    mainWallChart mainWallRadicand curvature wallAmplitude
  fun_prop

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.mainWallOriginalDensity_eq {h : ℝ} (hh : 0 < h) (z : SectionCoordinates) :
    mainWallOriginalDensity h z =
      (1 + 4 * wallAmplitude h (Real.exp (-z 1)) (Real.exp (-z 2))) * mainWallChartDensity h z := by
  have hH : 0 ≤ wallAmplitude h (Real.exp (-z 1)) (Real.exp (-z 2)) :=
    Real.rpow_nonneg (mul_pos (mul_pos hh (Real.exp_pos _)) (Real.exp_pos _)).le _
  unfold mainWallOriginalDensity mainWallChartDensity correctedSectionFluxDensity
  exact (mul_div_cancel₀ _ (by positivity : 1 + 4 * wallAmplitude h (Real.exp (-z 1))
    (Real.exp (-z 2)) ≠ 0)).symm

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.mainWallOriginalMeasure_eq_withDensity {h : ℝ} (hh : 0 < h) :
    mainWallOriginalMeasure h = (mainWallMeasure h).withDensity
      (fun z => ENNReal.ofReal (1 + 4 * wallAmplitude h (Real.exp (-z 1)) (Real.exp (-z 2)))) := by
  have hw : Measurable (fun z : SectionCoordinates =>
      ENNReal.ofReal (1 + 4 * wallAmplitude h (Real.exp (-z 1)) (Real.exp (-z 2)))) := by
    unfold wallAmplitude
    fun_prop
  unfold mainWallOriginalMeasure mainWallMeasure
  rw [← withDensity_mul _ (measurable_mainWallChartDensity h).ennreal_ofReal hw]
  apply withDensity_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  have hH : 0 ≤ wallAmplitude h (Real.exp (-z 1)) (Real.exp (-z 2)) :=
    Real.rpow_nonneg (mul_pos (mul_pos hh (Real.exp_pos _)) (Real.exp_pos _)).le _
  dsimp only [Pi.mul_apply]
  rw [mainWallOriginalDensity_eq hh, ENNReal.ofReal_mul (by positivity)]
  exact mul_comm _ _

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.mainWallOriginalMeasure_apply {h : ℝ} (hh : 0 < h) {A : Set SectionCoordinates}
    (hA : MeasurableSet A) :
    mainWallOriginalMeasure h A = ∫⁻ z in A,
      ENNReal.ofReal (1 + 4 * wallAmplitude h (Real.exp (-z 1)) (Real.exp (-z 2))) ∂mainWallMeasure h := by
  rw [mainWallOriginalMeasure_eq_withDensity hh, withDensity_apply _ hA]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.mainWallMeasure_le_original {h : ℝ} (hh : 0 < h) :
    mainWallMeasure h ≤ mainWallOriginalMeasure h := by
  rw [mainWallOriginalMeasure_eq_withDensity hh]
  have H : (fun _ : SectionCoordinates => (1 : ℝ≥0∞)) ≤ᵐ[mainWallMeasure h]
      (fun z => ENNReal.ofReal (1 + 4 * wallAmplitude h (Real.exp (-z 1)) (Real.exp (-z 2)))) := by
    apply Filter.Eventually.of_forall
    intro z
    have hH : 0 ≤ wallAmplitude h (Real.exp (-z 1)) (Real.exp (-z 2)) :=
      Real.rpow_nonneg (mul_pos (mul_pos hh (Real.exp_pos _)) (Real.exp_pos _)).le _
    exact ENNReal.one_le_ofReal.mpr (by linarith)
  simpa using withDensity_mono H

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.mainWallOriginalMeasure_null_iff {h : ℝ} (hh : 0 < h) (A : Set SectionCoordinates) :
    mainWallOriginalMeasure h A = 0 ↔ mainWallMeasure h A = 0 := by
  constructor
  · intro hA
    exact le_antisymm ((mainWallMeasure_le_original hh A).trans_eq hA) bot_le
  · intro hA
    rw [mainWallOriginalMeasure_eq_withDensity hh]
    exact withDensity_absolutelyContinuous _ _ hA

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.mainWallOriginalMeasure_le_of_small_walls {h : ℝ} (hh : 0 < h)
    {A : Set SectionCoordinates} (hA : MeasurableSet A)
    (hsmall : ∀ z ∈ A, Real.exp (-z 1) ≤ h ∧ Real.exp (-z 2) ≤ h) :
    mainWallOriginalMeasure h A ≤ ENNReal.ofReal (1 + 4 * h ^ 2) * mainWallMeasure h A := by
  rw [mainWallOriginalMeasure_apply hh hA]
  calc
    _ ≤ ∫⁻ _ in A, ENNReal.ofReal (1 + 4 * h ^ 2) ∂mainWallMeasure h := by
      apply setLIntegral_mono' hA
      intro z hz
      apply ENNReal.ofReal_le_ofReal
      have H := wallAmplitude_le_square hh.le (Real.exp_pos _).le (Real.exp_pos _).le
        (hsmall z hz).1 (hsmall z hz).2
      linarith
    _ = _ := by simp

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.signedShearLogCoordinates_radial_data {a d ε σ : ℝ} {z : SectionCoordinates}
    (ha : 0 < a) (hσ : |σ| = 1) (hz : z ∈ shearRadialDomain a d ε) :
    |signedShearLogCoordinates σ z 0| = z 0 ∧
    max (Real.exp (-(signedShearLogCoordinates σ z) 1))
      (Real.exp (-(signedShearLogCoordinates σ z) 2)) = max (z 1) (z 2) := by
  have hr : 0 < z 0 := ha.trans hz.2.2.1.1
  simp [signedShearLogCoordinates, abs_mul, hσ, abs_of_pos hr,
    Real.exp_log hz.1, Real.exp_log hz.2.1]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.orderedAngularLogCoordinates_radial_data {a d L : ℝ} {z : SectionCoordinates}
    (other : Bool) (ha : 0 < a) (hz : z ∈ angularRadialDomain other a d L) :
    |orderedAngularLogCoordinates other z 0| = |z 1| * z 0 ∧
    max (Real.exp (-(orderedAngularLogCoordinates other z) 1))
      (Real.exp (-(orderedAngularLogCoordinates other z) 2)) = z 0 := by
  have hr : 0 < z 0 := ha.trans hz.2.2.1.1
  have ho := hz.2.2.2.1
  cases other with
  | false =>
    simp [orderedAngularLogCoordinates, scaledAngularLogCoordinates, abs_mul, abs_of_pos hr,
      Real.exp_log hr, Real.exp_log hz.2.1, max_eq_left ho]
  | true =>
    simp [orderedAngularLogCoordinates, mainWallReflection, scaledAngularLogCoordinates,
      abs_mul, abs_of_pos hr, Real.exp_log hr, Real.exp_log hz.2.1,
      max_eq_right (le_of_lt ho)]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.physicalRadialPiece_subset_openSection {d ε : ℝ} (hd : 0 < d) (hε : ε ≤ 1)
    (i : RadialPieceIndex) : physicalRadialPiece d ε i ⊆ mainWallOpenSection d := by
  rcases i with ⟨neg | other, j⟩
  · rintro _ ⟨z, hz, rfl⟩
    have ha := dyadicScale_pos hd j
    obtain ⟨hs, hm⟩ := signedShearLogCoordinates_radial_data ha
      (show |(if neg then -1 else 1 : ℝ)| = 1 by cases neg <;> norm_num) hz
    change |signedShearLogCoordinates _ z 0| < d ∧
      max (Real.exp (-(signedShearLogCoordinates _ z) 1))
        (Real.exp (-(signedShearLogCoordinates _ z) 2)) < d
    rw [hs, hm]
    refine ⟨hz.2.2.2.2, (hz.2.2.2.1.trans ?_).trans_lt hz.2.2.2.2⟩
    have hr : 0 < z 0 := ha.trans hz.2.2.1.1
    nlinarith
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨hs, hm⟩ := orderedAngularLogCoordinates_radial_data other (dyadicScale_pos hd j) hz
    change |orderedAngularLogCoordinates other z 0| < d ∧
      max (Real.exp (-(orderedAngularLogCoordinates other z) 1))
        (Real.exp (-(orderedAngularLogCoordinates other z) 2)) < d
    rw [hs, hm]
    exact ⟨hz.2.2.2.2.2, hz.2.2.2.2.1⟩

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.volume_sectionCoordinate_level (i : Fin 3) (t : ℝ) :
    volume {z : SectionCoordinates | z i = t} = 0 := by
  exact Measure.pi_eval_preimage_null (fun _ : Fin 3 => (volume : Measure ℝ)) (measure_singleton t)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.volume_sectionWall_level (i : Fin 3) (t : ℝ) :
    volume {z : SectionCoordinates | Real.exp (-z i) = t} = 0 := by
  apply measure_mono_null (t := {z : SectionCoordinates | z i = -Real.log t})
    _ (volume_sectionCoordinate_level i _)
  intro z hz
  have H := congrArg Real.log hz
  rw [Real.log_exp] at H
  change z i = -Real.log t
  linarith

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.volume_mainWallRadialRadius_level (ε t : ℝ) :
    volume {z : SectionCoordinates | mainWallRadialRadius ε z = t} = 0 := by
  have hnull : volume (({z : SectionCoordinates | z 0 = t} ∪ {z | z 0 = -t}) ∪
      ({z | Real.exp (-z 1) = t} ∪ {z | Real.exp (-z 2) = t})) = 0 :=
    measure_union_null (measure_union_null (volume_sectionCoordinate_level 0 t)
      (volume_sectionCoordinate_level 0 (-t)))
      (measure_union_null (volume_sectionWall_level 1 t) (volume_sectionWall_level 2 t))
  apply measure_mono_null _ hnull
  intro z hz
  change mainWallRadialRadius ε z = t at hz
  unfold mainWallRadialRadius at hz
  split_ifs at hz
  · apply Or.inl
    rcases le_total 0 (z 0) with hs | hs
    · exact Or.inl (by simpa only [mem_ofPred_eq, abs_of_nonneg hs] using hz)
    · exact Or.inr (by rw [abs_of_nonpos hs] at hz; change z 0 = -t; linarith)
  · apply Or.inr
    rcases le_total (Real.exp (-z 1)) (Real.exp (-z 2)) with hw | hw
    · exact Or.inr (by simpa only [mem_ofPred_eq, max_eq_right hw] using hz)
    · exact Or.inl (by simpa only [mem_ofPred_eq, max_eq_left hw] using hz)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.volume_mainWallRadialBoundary (d ε : ℝ) : volume (mainWallRadialBoundary d ε) = 0 :=
  measure_mono_null inter_subset_right (measure_iUnion_null fun _ => volume_mainWallRadialRadius_level _ _)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.mainWallOriginalMeasure_radialBoundary (h d ε : ℝ) :
    mainWallOriginalMeasure h (mainWallRadialBoundary d ε) = 0 := by
  apply withDensity_absolutelyContinuous _ _
  exact Measure.absolutelyContinuous_restrict (volume_mainWallRadialBoundary d ε)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.radialFailurePiece_subset (d ε : ℝ) (F : RadialPieceIndex → Set SectionCoordinates)
    (i : RadialPieceIndex) : radialFailurePiece d ε F i ⊆ physicalRadialPiece d ε i :=
  image_mono inter_subset_left

end
end

private theorem BianchiIX.radialFailureSet_subset_openSection {d ε : ℝ} (hd : 0 < d) (hε : ε ≤ 1)
    (F : RadialPieceIndex → Set SectionCoordinates) : radialFailureSet d ε F ⊆ mainWallOpenSection d := by
  rintro z (hb | hp)
  · exact hb.1
  · obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    exact physicalRadialPiece_subset_openSection hd hε i (radialFailurePiece_subset d ε F i hi)


theorem solution {h q d ε P η σ Bcap BA BS : ℝ} {J : ℕ}
    (hh : 0 < h) (hd : 0 < d) (hd1 : d ≤ 1) (hdh : d ≤ h)
    (hε : 0 ≤ ε ∧ ε ≤ 1 / 128) (hL : 0 ≤ 1 / ε) (hP : 4 ≤ P)
    (hcap : Bcap ≤ 1) (hS : 800 * d ≤ Bcap) (hA : 51200 * (1 / ε + 1) * d ≤ Bcap)
    (hE : MeasurableSet (radialFailureSet d ε (restartRadialFailureFamily h q d ε P η J σ Bcap))) :
    mainWallOriginalMeasure h (radialFailureSet d ε (restartRadialFailureFamily h q d ε P η J σ Bcap)) ≤
      ENNReal.ofReal (1 + 4 * h ^ 2) *
        (mainWallMeasure h (angularFailureRegion h q d (1 / ε) P η J σ BA) +
          mainWallMeasure h (shearFailureRegion h q d ε P η J σ BS)) := by
  have hsub := restartRadialFailureSet_subset_regions (h := h) (q := q) (η := η) (J := J)
    (σ := σ) (BA := BA) (BS := BS) hd hd1 hε hL hP hcap hS hA
  have hB : mainWallMeasure h (mainWallRadialBoundary d ε) = 0 :=
    (mainWallOriginalMeasure_null_iff hh _).mp (mainWallOriginalMeasure_radialBoundary h d ε)
  have H : mainWallMeasure h (radialFailureSet d ε (restartRadialFailureFamily h q d ε P η J σ Bcap)) ≤
      mainWallMeasure h (angularFailureRegion h q d (1 / ε) P η J σ BA) +
        mainWallMeasure h (shearFailureRegion h q d ε P η J σ BS) := calc
    _ ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ = _ := by rw [hB, zero_add]
    _ ≤ _ := measure_union_le _ _
  have hsmall := radialFailureSet_subset_openSection hd (by linarith only [hε.2] : ε ≤ 1)
    (restartRadialFailureFamily h q d ε P η J σ Bcap)
  have HO := mainWallOriginalMeasure_le_of_small_walls hh hE (fun z hz =>
    ⟨(le_max_left _ _).trans ((hsmall hz).2.le.trans hdh),
      (le_max_right _ _).trans ((hsmall hz).2.le.trans hdh)⟩)
  exact HO.trans (mul_le_mul' le_rfl H)
