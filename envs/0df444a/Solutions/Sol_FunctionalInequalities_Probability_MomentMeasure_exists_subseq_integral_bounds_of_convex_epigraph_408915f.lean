-- Prove2me | solution 1 for FunctionalInequalities.Probability.MomentMeasure.exists_subseq_integral_bounds_of_convex_epigraph_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:38:59.384981+00:00
-- url     : https://prove2.me/submissions/f94c9da4-8d4d-4384-96b2-eaf299712002

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_RadialExtension
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
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.Bases
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic
import Theorems.Thm_FunctionalInequalities_Probability_MomentMeasure_limsup_mass_legendre_le_408915f
import Theorems.Thm_FunctionalInequalities_Probability_exists_subseq_lintegral_le_liminf_of_convex_epigraph_408915f

open MeasureTheory
open scoped ENNReal
noncomputable section
open Filter
open scoped Topology
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
namespace FunctionalInequalities.Probability.MomentMeasure
end FunctionalInequalities.Probability.MomentMeasure
open FunctionalInequalities.Probability.MomentMeasure in
/-- **CEK Lemma 17 (56).** The original uniformly integrable nonnegative convex
sequence has one subsequence and one genuine integrable convex limit satisfying
both semicontinuity inequalities. The original interior, radial and off-closure
outputs are retained. Finite dual mass is a derived output; zero mass is allowed.
Source mass need not be one, and zero dimension is included. -/
theorem solution
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (dx μ : Measure E) [dx.IsAddHaarMeasure] [IsFiniteMeasure μ]
    (h0 : (0 : E) ∈ interior (convexHull ℝ μ.support))
    (φ : ℕ → E → EReal) (hnn : ∀ ℓ x, 0 ≤ φ ℓ x) (hφ0 : ∀ ℓ, φ ℓ 0 = 0)
    (hconv : ∀ ℓ, Convex ℝ {p : E × ℝ | φ ℓ p.1 ≤ (p.2 : EReal)})
    (hmeas : ∀ ℓ, AEMeasurable (fun x => (φ ℓ x).toENNReal) μ)
    (hbdd : (⨆ ℓ, ∫⁻ x, (φ ℓ x).toENNReal ∂μ) ≠ ⊤) :
    ∃ (s : ℕ → ℕ) (ψ : E → EReal), StrictMono s ∧ (∀ x, 0 ≤ ψ x) ∧ ψ 0 = 0 ∧
      Convex ℝ {p : E × ℝ | ψ p.1 ≤ (p.2 : EReal)} ∧
      Measurable (fun x => (ψ x).toENNReal) ∧
      (∀ x ∈ interior (convexHull ℝ μ.support),
        ψ x ≠ ⊤ ∧ Tendsto (fun j => φ (s j) x) atTop (𝓝 (ψ x))) ∧
      (∀ x, Tendsto (fun t : ℝ => ψ (t • x)) (𝓝[<] 1) (𝓝 (ψ x))) ∧
      (∀ x ∉ closure (interior (convexHull ℝ μ.support)), ψ x = ⊤) ∧
      FunctionalInequalities.Probability.MomentMeasure.PotentialIntegrable ψ μ ∧ FunctionalInequalities.Probability.MomentMeasure.mass dx (FunctionalInequalities.Analysis.legendre ψ) ≠ ⊤ ∧
      (∫⁻ x, (ψ x).toENNReal ∂μ ≤
        liminf (fun j => ∫⁻ x, (φ (s j) x).toENNReal ∂μ) atTop) ∧
      limsup (fun j => FunctionalInequalities.Probability.MomentMeasure.mass dx (FunctionalInequalities.Analysis.legendre (φ (s j)))) atTop ≤ FunctionalInequalities.Probability.MomentMeasure.mass dx (FunctionalInequalities.Analysis.legendre ψ) := by
  obtain ⟨s, ψ, hs, hψnn, hψ0, hψconv, hψmeas, hlim, hrad, hoff, hfirst⟩ :=
    FunctionalInequalities.Probability.exists_subseq_lintegral_le_liminf_of_convex_epigraph_408915f
      μ h0 φ hnn hφ0 hconv hmeas hbdd
  have hbot : ∀ x, ψ x ≠ ⊥ := fun x => ne_of_gt (EReal.bot_lt_zero.trans_le (hψnn x))
  have hψfinite : (∫⁻ x, (ψ x).toENNReal ∂μ) ≠ ⊤ := by
    apply ne_top_of_le_ne_top hbdd
    apply hfirst.trans
    exact liminf_le_of_frequently_le' (Eventually.of_forall fun j =>
      le_iSup (fun ℓ => ∫⁻ x, (φ ℓ x).toENNReal ∂μ) (s j)).frequently
  have hpot : FunctionalInequalities.Probability.MomentMeasure.PotentialIntegrable ψ μ := by
    refine ⟨hbot, ?_, ?_⟩
    · filter_upwards [ae_lt_top hψmeas hψfinite] with x hx
      intro ht
      simp only [ht, EReal.toENNReal_top, lt_self_iff_false] at hx
    · have hi := integrable_toReal_of_lintegral_ne_top hψmeas.aemeasurable hψfinite
      simpa only [EReal.toReal_toENNReal (hψnn _)] using hi
  obtain ⟨hdualfinite, hsecond⟩ := FunctionalInequalities.Probability.MomentMeasure.limsup_mass_legendre_le_408915f dx
    (fun j => φ (s j)) ψ isOpen_interior (convex_convexHull ℝ μ.support).interior h0
    (fun x hx => ⟨(hlim x hx).1, hbot x⟩) (fun x hx => (hlim x hx).2) hrad hoff
  exact ⟨s, ψ, hs, hψnn, hψ0, hψconv, hψmeas, hlim, hrad, hoff,
    hpot, hdualfinite, hfirst, hsecond⟩
