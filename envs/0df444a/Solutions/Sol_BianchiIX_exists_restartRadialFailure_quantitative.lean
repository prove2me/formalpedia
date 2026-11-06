-- Prove2me | solution 1 for BianchiIX.exists_restartRadialFailure_quantitative
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T05:16:07.072766+00:00
-- url     : https://prove2.me/submissions/f3094297-d2a6-4548-bc2b-c4490b6bf170

import Definitions.Def_BianchiIX_Literature
import Definitions.Def_BianchiIX_RestartFluxData
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Statistics_EraStatistics
import Definitions.Def_BianchiIX_AxisAndOrbitData
import Definitions.Def_BianchiIX_AxisSectionMeasureData
import Definitions.Def_BianchiIX_RadialFailureData
import Definitions.Def_BianchiIX_EraCodingData
import Definitions.Def_BianchiIX_PhysicalFutureData
import Theorems.Thm_BianchiIX_exists_angularRegion_statistics
import Theorems.Thm_BianchiIX_exists_restartRadialFailure_partition
import Theorems.Thm_BianchiIX_exists_shearRegion_statistics
import Theorems.Thm_BianchiIX_mainWallOriginalMeasure_radialFailure_le_regions
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
open scoped ENNReal

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.logarithmicFluxConstant_nonneg {C δ : ℝ} (hC : 1 ≤ C) (hδ : 0 < δ) :
    0 ≤ logarithmicFluxConstant C δ := by
  have hlog := Real.log_nonneg hC
  unfold logarithmicFluxConstant
  positivity

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.logarithmicFluxConstantOne_nonneg {C σ : ℝ} (hC : 1 ≤ C) (hσ : 0 < σ) :
    0 ≤ logarithmicFluxConstantOne C σ := by
  have H := Real.log_nonneg hC
  unfold logarithmicFluxConstantOne
  positivity

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.angularFailureFluxConstant_ge_one {L σ : ℝ} (hL : 0 ≤ L) (hσ : 0 ≤ σ) :
    1 ≤ angularFailureFluxConstant L σ := by
  have hp : 1 ≤ (102400 * (L + 1)) ^ σ := Real.one_le_rpow (by linarith) hσ
  have hs : 1 ≤ Real.sqrt (3 : ℝ) := Real.one_le_sqrt.mpr (by norm_num)
  have H := mul_le_mul hs hp (by norm_num : (0 : ℝ) ≤ 1) (Real.sqrt_nonneg _)
  dsimp only [angularFailureFluxConstant]
  nlinarith only [H]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal Classical

private theorem BianchiIX.shearFailureFluxConstant_ge_one {σ : ℝ} (hσ : 0 ≤ σ) : 1 ≤ shearFailureFluxConstant σ := by
  have hp : 1 ≤ (800 : ℝ) ^ σ := Real.one_le_rpow (by norm_num) hσ
  have hs : 1 ≤ Real.sqrt (3 : ℝ) := Real.one_le_sqrt.mpr (by norm_num)
  have H := mul_le_mul hs hp (by norm_num : (0 : ℝ) ≤ 1) (Real.sqrt_nonneg _)
  dsimp only [shearFailureFluxConstant]
  nlinarith only [H]

end
end

/-- The fixed disjoint statistical failure set has both its exact flux integral and the quantitative finite-flux bound. -/
theorem solution (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bcap > (0 : ℝ), Bcap < 1 ∧ ∃ hstar > (0 : ℝ), hstar ≤ 1 / 8 ∧
          ∀ h ∈ Ioc (0 : ℝ) hstar, ∀ q D P : ℝ, 3 < q → 4 < D → 6 * D + 2 < P →
            ∀ ε ∈ Ioc (0 : ℝ) (1 / 128), ∃ C > (0 : ℝ),
              ∃ dstar > (0 : ℝ), dstar ≤ h / 8 ∧ ∀ d ∈ Ioc (0 : ℝ) dstar,
                let F := restartRadialFailureFamily h q d ε P η J σ Bcap
                let E := radialFailureSet d ε F
                (∀ i, MeasurableSet (F i)) ∧ MeasurableSet E ∧
                  mainWallOriginalMeasure h E = (∑' i, radialFailureIntegral h d ε F i) ∧
                  mainWallOriginalMeasure h E ≤ ENNReal.ofReal (C * d * (1 + |Real.log d|) ^ 2) ∧
                  mainWallOriginalMeasure h E ≠ ⊤ ∧
                  (∀ z ∈ mainWallOpenSection d \ E,
                    ∃ i : RadialPieceIndex, z ∈ physicalRadialPiece d ε i ∧
                      restartRadialOutput h q d ε i (radialPieceInverse i.1 z) ∈
                        EraSurvivor.typicalDomain η J σ Bcap) ∧
                  ∀ i z, z ∈ radialPieceDomain d ε i → z ∉ F i →
                    ∃ p : eraSurvivorDomain η J σ Bcap,
                      p.val = restartRadialOutput h q d ε i z ∧
                      EraStatistics (EraSurvivor.digits p) (EraSurvivor.phase p) := by
  obtain ⟨δG, hδG, hδmax, HG⟩ := exists_restartRadialFailure_partition hBirkhoff
  obtain ⟨δA, hδA, _, HA⟩ := exists_angularRegion_statistics hBirkhoff
  obtain ⟨δS, hδS, _, HS⟩ := exists_shearRegion_statistics hBirkhoff
  refine ⟨min δG (min δA δS), lt_min hδG (lt_min hδA hδS), (min_le_left _ _).trans hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσ1 hσJ
  obtain ⟨Bcap, hcap, hcap1, hG, hhG, hhG1, HG⟩ :=
    HG η hη (hηδ.trans (min_le_left _ _)) J hJ σ hσ hσ1 hσJ
  obtain ⟨BA, _, _, hA, hhA, HA⟩ :=
    HA η hη (hηδ.trans ((min_le_right _ _).trans (min_le_left _ _))) J hJ σ hσ hσ1 hσJ
  obtain ⟨BS, _, _, hS, hhS, HS⟩ :=
    HS η hη (hηδ.trans ((min_le_right _ _).trans (min_le_right _ _))) J hJ σ hσ hσ1 hσJ
  refine ⟨Bcap, hcap, hcap1, min hG (min hA hS), lt_min hhG (lt_min hhA hhS),
    (min_le_left _ _).trans hhG1, ?_⟩
  intro h hh q D P hq hD hP ε hε
  let L := 1 / ε
  have hL : 0 ≤ L := by dsimp only [L]; positivity [hε.1]
  let CA := 12 * L * logarithmicFluxConstantOne (angularFailureFluxConstant L σ) σ + 24 * L * P * Real.log 2
  let CS := 66 * logarithmicFluxConstant (shearFailureFluxConstant σ) σ + 132 * P ^ 2
  have hPpos : 0 < P := by linarith only [hD, hP]
  have hlog : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hCA : 0 ≤ CA := add_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) hL)
      (logarithmicFluxConstantOne_nonneg (angularFailureFluxConstant_ge_one hL hσ.le) hσ)) (by positivity)
  have hCS : 0 < CS := add_pos_of_nonneg_of_pos
    (mul_nonneg (by norm_num) (logarithmicFluxConstant_nonneg (shearFailureFluxConstant_ge_one hσ.le) hσ))
    (mul_pos (by norm_num) (sq_pos_of_pos hPpos))
  have hw : 0 < 1 + 4 * h ^ 2 := by positivity
  refine ⟨(1 + 4 * h ^ 2) * (3 * CA + CS),
    mul_pos hw (add_pos_of_nonneg_of_pos (by positivity) hCS), ?_⟩
  obtain ⟨dG, hdG, hdGh, HDG⟩ := HG h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q D P hq hD hP ε hε
  obtain ⟨dA, hdA, HDA⟩ := HA h ⟨hh.1, hh.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
    L hL q P hq (by linarith only [hD, hP])
  obtain ⟨dS, hdS, HDS⟩ := HS h ⟨hh.1, hh.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩ q D P hq hD hP
  let K := 51200 * (L + 1)
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨min dG (min dA (min dS (min 1 (min (Bcap / 800) (Bcap / K))))),
    lt_min hdG (lt_min hdA (lt_min hdS (lt_min zero_lt_one
      (lt_min (div_pos hcap (by norm_num)) (div_pos hcap hK))))),
    (min_le_left _ _).trans hdGh, ?_⟩
  intro d hd F E
  have hd' := hd.2.trans (min_le_right _ _)
  have hd'' := hd'.trans (min_le_right _ _)
  have hd''' := hd''.trans (min_le_right _ _)
  have hdnum := hd'''.trans (min_le_right _ _)
  have hdG' : d ≤ dG := hd.2.trans (min_le_left _ _)
  have hd1 : d ≤ 1 := hd'''.trans (min_le_left _ _)
  have hdh : d ≤ h := by linarith only [hdG'.trans hdGh, hh.1]
  have hSd : 800 * d ≤ Bcap := by
    have H := (le_div_iff₀ (by norm_num : (0 : ℝ) < 800)).mp (hdnum.trans (min_le_left _ _))
    nlinarith only [H]
  have hAd : K * d ≤ Bcap := by
    have H := (le_div_iff₀ hK).mp (hdnum.trans (min_le_right _ _))
    nlinarith only [H]
  obtain ⟨hF, hE, Heq, Hgood, Hstats⟩ := HDG d ⟨hd.1, hdG'⟩
  obtain ⟨_, HAbound, _, _⟩ := HDA d ⟨hd.1, hd'.trans (min_le_left _ _)⟩
  obtain ⟨_, HSbound, _, _⟩ := HDS d ⟨hd.1, hd''.trans (min_le_left _ _)⟩ ε ⟨hε.1.le, hε.2⟩
  have Hregions := mainWallOriginalMeasure_radialFailure_le_regions (BA := BA) (BS := BS)
    hh.1 hd.1 hd1 hdh ⟨hε.1.le, hε.2⟩ hL (by linarith only [hD, hP]) hcap1.le hSd hAd hE
  have hweight : 1 + |Real.log d| + 2 * Real.log 2 ≤ 3 * (1 + |Real.log d|) ^ 2 := by
    have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    nlinarith only [hlog2, abs_nonneg (Real.log d), sq_nonneg (Real.log d)]
  have HA' : mainWallMeasure h (angularFailureRegion h q d L P η J σ BA) ≤
      ENNReal.ofReal (3 * CA * d * (1 + |Real.log d|) ^ 2) :=
    HAbound.trans (ENNReal.ofReal_le_ofReal
      ((mul_le_mul_of_nonneg_left hweight (mul_nonneg hCA hd.1.le)).trans_eq (by ring)))
  have Hbound : mainWallOriginalMeasure h E ≤
      ENNReal.ofReal ((1 + 4 * h ^ 2) * (3 * CA + CS) * d * (1 + |Real.log d|) ^ 2) := calc
    _ ≤ _ := Hregions
    _ ≤ ENNReal.ofReal (1 + 4 * h ^ 2) *
        (ENNReal.ofReal (3 * CA * d * (1 + |Real.log d|) ^ 2) +
          ENNReal.ofReal (CS * d * (1 + |Real.log d|) ^ 2)) := mul_le_mul' le_rfl (add_le_add HA' HSbound)
    _ = _ := by
      rw [← ENNReal.ofReal_add
        (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCA) hd.1.le) (sq_nonneg _))
        (mul_nonneg (mul_nonneg hCS.le hd.1.le) (sq_nonneg _)), ← ENNReal.ofReal_mul hw.le]
      congr 1
      ring
  exact ⟨hF, hE, Heq, Hbound, ne_top_of_le_ne_top ENNReal.ofReal_ne_top Hbound, Hgood, Hstats⟩
