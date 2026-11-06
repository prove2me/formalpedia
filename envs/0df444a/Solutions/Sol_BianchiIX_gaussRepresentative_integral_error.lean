-- Prove2me | solution 1 for BianchiIX.gaussRepresentative_integral_error
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T19:22:26.565721+00:00
-- url     : https://prove2.me/submissions/e1b3bfee-73bd-4eb1-9e1f-71b66ea429af

import Definitions.Def_BianchiIX_Statistics_GaussContinuous
import Theorems.Thm_BianchiIX_gaussMass_hasSum
import Theorems.Thm_BianchiIX_gaussMass_nonneg
import Theorems.Thm_BianchiIX_hasSum_gaussCylinder_integral
import Theorems.Thm_BianchiIX_measurableSet_gaussCylinder
import Theorems.Thm_BianchiIX_summable_probability_weighted
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.Induction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
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

open Set Filter MeasureTheory
open scoped Topology ENNReal
open BianchiIX
noncomputable section
open InverseBranchTree.BranchEstimates


theorem solution {f : ℝ → ℝ} (hf : Integrable f gaussMeasure)
    (n : ℕ) {M ε : ℝ} (hb : ∀ w, |f (gaussRepresentative n w)| ≤ M)
    (hosc : ∀ (w : GaussWords n) x, x ∈ gaussCylinder w.val →
      |f x - f (gaussRepresentative n w)| ≤ ε) :
    |(∫ x, f x ∂gaussMeasure) - ∑' w, gaussMass n w * f (gaussRepresentative n w)| ≤ ε := by
  have hi := hasSum_gaussCylinder_integral hf n
  have hr := summable_probability_weighted (gaussMass_nonneg n) (gaussMass_hasSum n) hb
  have hd := (hi.summable.sub hr).abs
  have hcell (w : GaussWords n) :
      |(∫ x in gaussCylinder w.val, f x ∂gaussMeasure) -
        gaussMass n w * f (gaussRepresentative n w)| ≤ ε * gaussMass n w := by
    have hbound := norm_setIntegral_le_of_norm_le_const_ae
      (measure_lt_top gaussMeasure (gaussCylinder w.val))
      ((ae_restrict_mem (measurableSet_gaussCylinder w.val)).mono
        (fun x hx => (show ‖f x - f (gaussRepresentative n w)‖ ≤ ε from
          (Real.norm_eq_abs _).trans_le (hosc w x hx))))
    rw [integral_sub hf.integrableOn (integrable_const _), setIntegral_const] at hbound
    simpa only [Real.norm_eq_abs, smul_eq_mul, Measure.real, gaussMass] using hbound
  rw [← hi.tsum_eq, ← hi.summable.tsum_sub hr]
  calc
    _ ≤ ∑' w : GaussWords n, |(∫ x in gaussCylinder w.val, f x ∂gaussMeasure) -
        gaussMass n w * f (gaussRepresentative n w)| := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm
        (f := fun w : GaussWords n => (∫ x in gaussCylinder w.val, f x ∂gaussMeasure) -
          gaussMass n w * f (gaussRepresentative n w))
        (by simpa only [Real.norm_eq_abs] using hd)
    _ ≤ ∑' w, ε * gaussMass n w := hd.tsum_le_tsum hcell ((gaussMass_hasSum n).summable.mul_left ε)
    _ = ε := by rw [tsum_mul_left, (gaussMass_hasSum n).tsum_eq, mul_one]
