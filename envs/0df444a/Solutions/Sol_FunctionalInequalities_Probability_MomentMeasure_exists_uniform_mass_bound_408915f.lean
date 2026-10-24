-- Prove2me | solution 1 for FunctionalInequalities.Probability.MomentMeasure.exists_uniform_mass_bound_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:38:57.973171+00:00
-- url     : https://prove2.me/submissions/13be1622-4107-4687-96d8-51bd488c4a0e

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Affine
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_MomentMeasure_Basic
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Data.EReal.Operations
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic
import Theorems.Thm_FunctionalInequalities_Probability_MomentMeasure_density_scaled_le_exp_408915f
import Theorems.Thm_FunctionalInequalities_Probability_MomentMeasure_exists_uniform_legendre_lower_408915f
import Theorems.Thm_FunctionalInequalities_Probability_integrable_exp_sub_norm_408915f

section
noncomputable section
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- Every affine summand of the actual extended-real conjugate is continuous,
including when its fixed intercept is an infinite value. -/
theorem FunctionalInequalities.Analysis.continuous_legendre_summand (φ : E → EReal) (x : E) :
    Continuous (fun y : E => (inner ℝ x y : EReal) - φ x) := by
  by_cases hb : φ x = ⊥
  · simpa only [hb, EReal.coe_sub_bot] using
      (continuous_const : Continuous (fun _ : E => (⊤ : EReal)))
  by_cases ht : φ x = ⊤
  · simpa only [ht, EReal.sub_top] using
      (continuous_const : Continuous (fun _ : E => (⊥ : EReal)))
  lift φ x to ℝ using ⟨ht, hb⟩ with r hr
  have hc : Continuous (fun y : E => inner ℝ x y - r) :=
    (continuous_const.inner continuous_id).sub continuous_const
  simpa only [Function.comp_def, ← hr, ← EReal.coe_sub] using continuous_coe_real_ereal.comp hc
/-- The conjugate is lower semicontinuous for any extended-real input;
no properness, convexity, finite dimension or global finiteness is required. -/
theorem FunctionalInequalities.Analysis.lowerSemicontinuous_legendre (φ : E → EReal) :
    LowerSemicontinuous (legendre φ) := by
  exact lowerSemicontinuous_iSup (fun x =>
    (continuous_legendre_summand φ x).lowerSemicontinuous)
end
end
end
end

section
noncomputable section
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
section
namespace FunctionalInequalities.Probability.MomentMeasure
end FunctionalInequalities.Probability.MomentMeasure
open FunctionalInequalities FunctionalInequalities.Probability FunctionalInequalities.Probability.MomentMeasure
open MeasureTheory
open scoped ENNReal
open FunctionalInequalities.Analysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- The density of the actual conjugate is Borel even for a nonmeasurable primal. -/
theorem FunctionalInequalities.Probability.MomentMeasure.measurable_density_legendre [MeasurableSpace E] [BorelSpace E] (φ : E → EReal) :
    Measurable (density (legendre φ)) :=
  EReal.measurable_exp.comp (lowerSemicontinuous_legendre φ).measurable.neg
end
end
end
end
end

noncomputable section
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
section
namespace FunctionalInequalities.Probability.MomentMeasure
end FunctionalInequalities.Probability.MomentMeasure
open FunctionalInequalities FunctionalInequalities.Probability FunctionalInequalities.Probability.MomentMeasure
open FunctionalInequalities.Analysis
section
open MeasureTheory Filter Set
open scoped ENNReal Topology
section Geometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- Genuine Haar change of variables for nonnegative integrals, retaining
infinite integrals. There is no integrability or finite-mass premise. -/
theorem FunctionalInequalities.Probability.MomentMeasure.lintegral_eq_pow_mul_smul (dx : Measure E) [dx.IsAddHaarMeasure]
    (f : E → ℝ≥0∞) (hf : Measurable f) {a : ℝ} (ha : 0 < a) :
    (∫⁻ y, f y ∂dx) = ENNReal.ofReal (a ^ Module.finrank ℝ E) * ∫⁻ y, f (a • y) ∂dx := by
  have hm := lintegral_map hf (measurable_const_smul a) (μ := dx)
  rw [Measure.map_addHaar_smul dx ha.ne', lintegral_smul_measure, smul_eq_mul,
    abs_of_pos (inv_pos.mpr (pow_pos ha _)), ENNReal.ofReal_inv_of_pos (pow_pos ha _)] at hm
  calc
    (∫⁻ y, f y ∂dx) = ENNReal.ofReal (a ^ Module.finrank ℝ E) *
        ((ENNReal.ofReal (a ^ Module.finrank ℝ E))⁻¹ * ∫⁻ y, f y ∂dx) := by
      rw [← mul_assoc, ENNReal.mul_inv_cancel
        (ne_of_gt (ENNReal.ofReal_pos.mpr (pow_pos ha _))) ENNReal.ofReal_ne_top, one_mul]
    _ = _ := by rw [hm]
namespace FunctionalInequalities.Probability.MomentMeasure
end FunctionalInequalities.Probability.MomentMeasure
open FunctionalInequalities.Probability.MomentMeasure in
/-- A genuine polynomial bound, with A selected before the potential.
The fixed dominator and its finite Haar integral are derived from Lemma16 and
the actual finite simplex. max(M,1) retains the small-M regime. -/
theorem solution (dx μ : Measure E) [dx.IsAddHaarMeasure] [IsFiniteMeasure μ]
    (h0 : (0 : E) ∈ interior (convexHull ℝ μ.support)) :
    ∃ A : ℝ, 0 < A ∧ ∀ φ : E → EReal,
      (∀ x, 0 ≤ φ x) → φ 0 = 0 → FunctionalInequalities.Analysis.ConvexPotential φ → FunctionalInequalities.Probability.MomentMeasure.PotentialIntegrable φ μ →
      FunctionalInequalities.Probability.MomentMeasure.mass dx (FunctionalInequalities.Analysis.legendre φ) ≤ ENNReal.ofReal
        (A * (max (∫ x, (φ x).toReal ∂μ) 1) ^ Module.finrank ℝ E) := by
  obtain ⟨c, C, hc, hC, hlower⟩ := FunctionalInequalities.Probability.MomentMeasure.exists_uniform_legendre_lower_408915f μ h0
  let D : E → ℝ≥0∞ := fun y => ENNReal.ofReal (Real.exp (C - c * ‖y‖))
  let Z : ℝ≥0∞ := ∫⁻ y, D y ∂dx
  have hZ : Z ≠ ⊤ := (lintegral_ofReal_ne_top_iff_integrable
    (FunctionalInequalities.Probability.integrable_exp_sub_norm_408915f dx hc C).aestronglyMeasurable
    (Eventually.of_forall fun _ => (Real.exp_pos _).le)).mpr (FunctionalInequalities.Probability.integrable_exp_sub_norm_408915f dx hc C)
  let A : ℝ := max Z.toReal 1
  have hA : 0 < A := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hZA : Z ≤ ENNReal.ofReal A := by
    rw [← ENNReal.ofReal_toReal hZ]
    exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
  refine ⟨A, hA, ?_⟩
  intro φ hnn hφ0 hconv hφ
  let M : ℝ := ∫ x, (φ x).toReal ∂μ
  let a : ℝ := max M 1
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hscaled : (∫⁻ y, FunctionalInequalities.Probability.MomentMeasure.density (FunctionalInequalities.Analysis.legendre φ) (a • y) ∂dx) ≤ Z :=
    lintegral_mono (FunctionalInequalities.Probability.MomentMeasure.density_scaled_le_exp_408915f φ hC.le (le_max_right _ _) (le_max_left _ _)
      (hlower φ hnn hφ0 hconv hφ))
  calc
    FunctionalInequalities.Probability.MomentMeasure.mass dx (FunctionalInequalities.Analysis.legendre φ) = ENNReal.ofReal (a ^ Module.finrank ℝ E) *
        ∫⁻ y, FunctionalInequalities.Probability.MomentMeasure.density (FunctionalInequalities.Analysis.legendre φ) (a • y) ∂dx :=
      FunctionalInequalities.Probability.MomentMeasure.lintegral_eq_pow_mul_smul dx _ (FunctionalInequalities.Probability.MomentMeasure.measurable_density_legendre φ) ha
    _ ≤ ENNReal.ofReal (a ^ Module.finrank ℝ E) * ENNReal.ofReal A :=
      mul_le_mul' le_rfl (hscaled.trans hZA)
    _ = _ := by rw [← ENNReal.ofReal_mul (pow_pos ha _).le, mul_comm]
