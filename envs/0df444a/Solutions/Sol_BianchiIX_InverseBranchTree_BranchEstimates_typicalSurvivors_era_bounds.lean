-- Prove2me | solution 1 for BianchiIX.InverseBranchTree.BranchEstimates.typicalSurvivors_era_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T20:17:50.726193+00:00
-- url     : https://prove2.me/submissions/4dc5c13f-dc46-4250-bb03-e320e50e4f55

import Definitions.Def_BianchiIX_Literature
import Definitions.Def_BianchiIX_Analysis_AmplitudeSequence
import Definitions.Def_BianchiIX_Statistics_TreeDistortion
import Definitions.Def_BianchiIX_Statistics_TreeOrbits
import Definitions.Def_BianchiIX_Statistics_EraStatistics
import Definitions.Def_BianchiIX_Statistics_EraBudget
import Theorems.Thm_BianchiIX_InverseBranchTree_BranchEstimates_eraStatistics_on_typicalSurvivors
import Theorems.Thm_BianchiIX_InverseBranchTree_BranchEstimates_restricted_loss_of_amplitude_bounds
import Theorems.Thm_BianchiIX_InverseBranchTree_BranchEstimates_typicalSurvivors_ae_eq
import Theorems.Thm_BianchiIX_InverseBranchTree_survivors_subset_root
import Theorems.Thm_BianchiIX_InverseBranchTree_typicalSurvivors_measurable
import Theorems.Thm_BianchiIX_InverseBranchTree_typicalSurvivors_subset
import Theorems.Thm_BianchiIX_era_distortion_budget
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Data.List.Induction
import Mathlib.Data.PNat.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Data.Rat.Floor
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.OrderIsoNat
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Dynamics.BirkhoffSum.NormedSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology ENNReal
open BianchiIX.InverseBranchTree
open BianchiIX.InverseBranchTree.BranchEstimates


/-- The canonical typical survivor set satisfies every statistical conclusion and the restricted loss bound. -/
theorem solution {T : InverseBranchTree} {B η Cv Ci : ℝ}
    (E : T.BranchEstimates (fun m => Cv * eraAmplitude B m)
      (fun m => Ci * Real.sqrt (eraAmplitude B m)))
    (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) (hroot : T.root = Ioo (0 : ℝ) 1)
    (hB : 0 < B) (hB1 : B ≤ 1) (hη : 0 ≤ η) (hηhalf : η ≤ 1 / 2)
    (hsmall : B ^ η < 1 / 160) (hCv : 0 ≤ Cv) (hCi : 0 ≤ Ci)
    (hL : 2 * Ci * Real.sqrt B + 4 * Cv * B ^ (4 / 3 : ℝ) ≤ Real.log 2)
    (hsize : ∀ w, volume (T.stoppedDomain w) ≤ ENNReal.ofReal (10 * eraAmplitude B w.length ^ η)) :
    (1 / 2 : ℝ≥0∞) < volume T.typicalSurvivors ∧
      (∀ I : Set ℝ, volume ((I ∩ T.root) \ (I ∩ T.typicalSurvivors)) ≤
        min (volume I) (ENNReal.ofReal (80 * B ^ η))) ∧
      ∀ x : T.survivors, x.val ∈ T.typicalSurvivors → EraStatistics (T.digits x) (T.phase x) := by
  have hb := era_distortion_budget hB hB1 hη hηhalf hsmall hCv hCi
  have heq := E.typicalSurvivors_ae_eq hBirkhoff hb.2.2
  have hloss (I : Set ℝ) : volume ((I ∩ T.root) \ (I ∩ T.typicalSurvivors)) ≤
      min (volume I) (ENNReal.ofReal (80 * B ^ η)) := by
    have hm : volume ((I ∩ T.root) \ (I ∩ T.typicalSurvivors)) =
        volume ((I ∩ T.root) \ (I ∩ T.survivors)) :=
      measure_congr (ae_eq_set_sdiff (ae_eq_refl (I ∩ T.root : Set ℝ))
        (ae_eq_set_inter (ae_eq_refl I) heq))
    exact hm.trans_le
      (E.restricted_loss_of_amplitude_bounds hB hB1 hη hηhalf hsmall hCv hCi hL hsize I)
  have hloss0 : volume (T.root \ T.typicalSurvivors) ≤ ENNReal.ofReal (80 * B ^ η) := by
    simpa only [univ_inter] using (hloss univ).trans (min_le_right _ _)
  have hhalf : ENNReal.ofReal (80 * B ^ η) < (1 / 2 : ℝ≥0∞) := by
    have H : 80 * B ^ η < (1 / 2 : ℝ) := by linarith
    convert! (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1 / 2)).mpr H using 1
    norm_num [ENNReal.ofReal_div_of_pos]
  have hmass : (1 / 2 : ℝ≥0∞) < volume T.typicalSurvivors := by
    have hsplit := measure_sdiff_add_inter (μ := volume) T.root T.typicalSurvivors_measurable
    rw [inter_eq_right.mpr (T.typicalSurvivors_subset.trans T.survivors_subset_root),
      hroot, Real.volume_Ioo] at hsplit
    norm_num at hsplit
    by_contra h
    have hle := le_of_not_gt h
    have hfinite : volume T.typicalSurvivors ≠ ⊤ := ne_top_of_le_ne_top (by norm_num) hle
    have H := ENNReal.add_lt_add_of_lt_of_le hfinite (hloss0.trans_lt hhalf) hle
    rw [hroot, hsplit] at H
    have htwo : (1 / 2 : ℝ≥0∞) + 1 / 2 = 1 := by
      rw [← ENNReal.add_div, show (1 : ℝ≥0∞) + 1 = 2 by norm_num]
      exact ENNReal.div_self (by norm_num) (by norm_num)
    exact (not_lt_of_ge htwo.le) H
  exact ⟨hmass, hloss, E.eraStatistics_on_typicalSurvivors hb.1.tendsto_atTop_zero⟩
