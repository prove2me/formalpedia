-- Prove2me | solution 1 for FunctionalInequalities.Probability.MomentMeasure.limsup_mass_legendre_le_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:29:45.059754+00:00
-- url     : https://prove2.me/submissions/3225ea3c-c336-4625-80b6-35e292b5a6d9

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_MomentMeasure_Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Data.EReal.Operations
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic
import Theorems.Thm_FunctionalInequalities_Analysis_legendre_eq_interior_sup_408915f
import Theorems.Thm_FunctionalInequalities_Probability_MomentMeasure_exists_integrable_exponential_domination_408915f
import Theorems.Thm_FunctionalInequalities_Probability_MomentMeasure_limsup_density_legendre_le_408915f

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
open MeasureTheory Filter Set
open scoped ENNReal Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section
namespace FunctionalInequalities.Probability.MomentMeasure
end FunctionalInequalities.Probability.MomentMeasure
open FunctionalInequalities FunctionalInequalities.Probability FunctionalInequalities.Probability.MomentMeasure
open FunctionalInequalities.Analysis
section FiniteDimensional
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
namespace FunctionalInequalities.Probability.MomentMeasure
end FunctionalInequalities.Probability.MomentMeasure
open FunctionalInequalities.Probability.MomentMeasure in
/-- CEK Lemma 17 (56b) for the actual limit already delivered by (56a).
Only the original interior convergence and actual radial extension are inputs;
the finite affine comparison, domination and mass finiteness are all proved. -/
theorem solution
    (dx : Measure E) [dx.IsAddHaarMeasure]
    (φ : ℕ → E → EReal) (ψ : E → EReal) {K : Set E}
    (hK : IsOpen K) (hKconv : Convex ℝ K) (h0 : (0 : E) ∈ K)
    (hfin : ∀ x ∈ K, ψ x ≠ ⊤ ∧ ψ x ≠ ⊥)
    (hlim : ∀ x ∈ K, Tendsto (fun j => φ j x) atTop (𝓝 (ψ x)))
    (hrad : ∀ x, Tendsto (fun t : ℝ => ψ (t • x)) (𝓝[<] 1) (𝓝 (ψ x)))
    (hoff : ∀ x ∉ closure K, ψ x = ⊤) :
    FunctionalInequalities.Probability.MomentMeasure.mass dx (FunctionalInequalities.Analysis.legendre ψ) ≠ ⊤ ∧
      limsup (fun j => FunctionalInequalities.Probability.MomentMeasure.mass dx (FunctionalInequalities.Analysis.legendre (φ j))) atTop ≤ FunctionalInequalities.Probability.MomentMeasure.mass dx (FunctionalInequalities.Analysis.legendre ψ) := by
  obtain ⟨c, M, N, _hc, hfinite, hψbound, hφbound⟩ :=
    FunctionalInequalities.Probability.MomentMeasure.exists_integrable_exponential_domination_408915f dx φ ψ hK h0 hfin hlim
  have hpoint : ∀ y, limsup (fun j => FunctionalInequalities.Probability.MomentMeasure.density (FunctionalInequalities.Analysis.legendre (φ j)) y) atTop ≤
      FunctionalInequalities.Probability.MomentMeasure.density (FunctionalInequalities.Analysis.legendre ψ) y :=
    FunctionalInequalities.Probability.MomentMeasure.limsup_density_legendre_le_408915f φ ψ hlim (FunctionalInequalities.Analysis.legendre_eq_interior_sup_408915f hK hKconv h0 ψ hrad hoff)
  refine ⟨ne_top_of_le_ne_top hfinite (lintegral_mono hψbound), ?_⟩
  have htail := limsup_lintegral_le
    (fun y => ENNReal.ofReal (Real.exp (M - c * ‖y‖)))
    (fun j => FunctionalInequalities.Probability.MomentMeasure.measurable_density_legendre (φ (j + N)))
    (fun j => Eventually.of_forall (hφbound (j + N) (Nat.le_add_left _ _))) hfinite
  change limsup (fun j => FunctionalInequalities.Probability.MomentMeasure.mass dx (FunctionalInequalities.Analysis.legendre (φ (j + N)))) atTop ≤ _ at htail
  rw [limsup_nat_add (fun j => FunctionalInequalities.Probability.MomentMeasure.mass dx (FunctionalInequalities.Analysis.legendre (φ j))) N] at htail
  calc
    limsup (fun j => FunctionalInequalities.Probability.MomentMeasure.mass dx (FunctionalInequalities.Analysis.legendre (φ j))) atTop
        ≤ ∫⁻ y, limsup (fun j => FunctionalInequalities.Probability.MomentMeasure.density (FunctionalInequalities.Analysis.legendre (φ (j + N))) y) atTop ∂dx := htail
    _ = ∫⁻ y, limsup (fun j => FunctionalInequalities.Probability.MomentMeasure.density (FunctionalInequalities.Analysis.legendre (φ j)) y) atTop ∂dx := by
      apply lintegral_congr
      intro y
      exact limsup_nat_add (fun j => FunctionalInequalities.Probability.MomentMeasure.density (FunctionalInequalities.Analysis.legendre (φ j)) y) N
    _ ≤ FunctionalInequalities.Probability.MomentMeasure.mass dx (FunctionalInequalities.Analysis.legendre ψ) := lintegral_mono hpoint
