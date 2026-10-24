-- Prove2me | solution 1 for FunctionalInequalities.Probability.MomentMeasure.exists_uniform_legendre_lower_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:37:53.756415+00:00
-- url     : https://prove2.me/submissions/9d51b4cd-efc0-4c97-9deb-3034c3683fb7

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
import Theorems.Thm_FunctionalInequalities_Analysis_affineMaximum_coercive_408915f
import Theorems.Thm_FunctionalInequalities_Probability_exists_pos_le_mul_lintegral_toReal_of_convex_epigraph_408915f

section
noncomputable section
open Filter Set
open scoped Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- A simplex in the original open neighborhood supplies a finite witness whose
convex hull still contains a neighborhood of zero, including dimension zero. -/
theorem FunctionalInequalities.Analysis.exists_finite_hull_neighborhood [FiniteDimensional ℝ E]
    {K : Set E} (hK : IsOpen K) (h0 : (0 : E) ∈ K) :
    ∃ (s : Finset E) (_hs : s.Nonempty), (↑s : Set E) ⊆ K ∧
      (0 : E) ∈ interior (convexHull ℝ (↑s : Set E)) := by
  classical
  obtain ⟨b, hb0, hbK⟩ := exists_mem_interior_convexHull_affineBasis (hK.mem_nhds h0)
  let s : Finset E := Finset.univ.image b
  have heq : (↑s : Set E) = range b := by simp [s]
  refine ⟨s, Finset.univ_nonempty.image b, ?_, ?_⟩
  · rw [heq]
    exact (subset_convexHull ℝ (range b)).trans hbK
  · rwa [heq]
/-- Finite affine maxima are genuine lower bounds of the full conjugate. -/
theorem FunctionalInequalities.Analysis.affineMaximum_le_legendre (ψ : E → EReal) (s : Finset E) (hs : s.Nonempty)
    (hfin : ∀ x ∈ s, ψ x ≠ ⊤ ∧ ψ x ≠ ⊥) (y : E) :
    (affineMaximum s hs (fun x => (ψ x).toReal) y : EReal) ≤ legendre ψ y := by
  obtain ⟨x, hx, heq⟩ := s.exists_mem_eq_sup' hs (fun x => inner ℝ x y - (ψ x).toReal)
  change ((s.sup' hs (fun x => inner ℝ x y - (ψ x).toReal) : ℝ) : EReal) ≤ _
  rw [heq, EReal.coe_sub, EReal.coe_toReal (hfin x hx).1 (hfin x hx).2]
  exact le_iSup (fun z : E => (inner ℝ z y : EReal) - ψ z) x
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
section Integral
variable {E : Type*} [MeasurableSpace E] {μ : Measure E}
/-- Source admissibility and nonnegativity identify the actual extended integral,
including its a.e. finite guard; infinity is never totalized before this step. -/
theorem FunctionalInequalities.Probability.MomentMeasure.lintegral_nonneg_potential (φ : E → EReal) (hφ : PotentialIntegrable φ μ)
    (hnn : ∀ x, 0 ≤ φ x) :
    AEMeasurable (fun x => (φ x).toENNReal) μ ∧
      (∫⁻ x, (φ x).toENNReal ∂μ) = ENNReal.ofReal (∫ x, (φ x).toReal ∂μ) ∧
      0 ≤ ∫ x, (φ x).toReal ∂μ := by
  have heq : (fun x => (φ x).toENNReal) =ᵐ[μ] (fun x => ENNReal.ofReal (φ x).toReal) := by
    filter_upwards [hφ.2.1] with x hx
    exact EReal.toENNReal_of_ne_top hx
  have hm := hφ.2.2.aemeasurable.ennreal_ofReal
  refine ⟨hm.congr heq.symm, ?_, integral_nonneg (fun x => EReal.toReal_nonneg (hnn x))⟩
  rw [lintegral_congr_ae heq]
  exact (ofReal_integral_eq_lintegral_ofReal hφ.2.2
    (Eventually.of_forall fun x => EReal.toReal_nonneg (hnn x))).symm
end Integral
section Geometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
namespace FunctionalInequalities.Probability.MomentMeasure
end FunctionalInequalities.Probability.MomentMeasure
open FunctionalInequalities.Probability.MomentMeasure in
/-- Constants are chosen from the measure and one fixed finite simplex before
any potential. Lemma16 produces every vertex bound, and the actual affine
maximum converts it to linear growth of the actual conjugate. -/
theorem solution (μ : Measure E) [IsFiniteMeasure μ]
    (h0 : (0 : E) ∈ interior (convexHull ℝ μ.support)) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ φ : E → EReal,
      (∀ x, 0 ≤ φ x) → φ 0 = 0 → FunctionalInequalities.Analysis.ConvexPotential φ → FunctionalInequalities.Probability.MomentMeasure.PotentialIntegrable φ μ →
      ∀ y, 0 ≤ FunctionalInequalities.Analysis.legendre φ y ∧
        ((c * ‖y‖ - C * (∫ x, (φ x).toReal ∂μ) : ℝ) : EReal) ≤ FunctionalInequalities.Analysis.legendre φ y := by
  classical
  let K := interior (convexHull ℝ μ.support)
  obtain ⟨s, hs, hsK, hs0⟩ := FunctionalInequalities.Analysis.exists_finite_hull_neighborhood (K := K) isOpen_interior h0
  obtain ⟨c, hc, hcoerc⟩ := FunctionalInequalities.Analysis.affineMaximum_coercive_408915f s hs hs0
  have hp : ∀ x : {x : E // x ∈ s}, ∃ C : ℝ, 0 < C ∧ ∀ φ : E → EReal,
      (∀ y, 0 ≤ φ y) → Convex ℝ {p : E × ℝ | φ p.1 ≤ (p.2 : EReal)} →
      AEMeasurable (fun y => (φ y).toENNReal) μ → (∫⁻ y, (φ y).toENNReal ∂μ) ≠ ⊤ →
        φ x ≤ ((C * (∫⁻ y, (φ y).toENNReal ∂μ).toReal : ℝ) : EReal) := by
    intro x
    exact FunctionalInequalities.Probability.exists_pos_le_mul_lintegral_toReal_of_convex_epigraph_408915f
      μ x (hsK x.2)
  choose Cs hCs hpoint using hp
  let C : ℝ := ∑ x ∈ s.attach, Cs x
  have hCle (x : {x : E // x ∈ s}) : Cs x ≤ C :=
    Finset.single_le_sum (fun i _ => (hCs i).le) (s.mem_attach x)
  have hs_copy := hs
  obtain ⟨x0, hx0⟩ := hs_copy
  have hC : 0 < C := (hCs ⟨x0, hx0⟩).trans_le (hCle ⟨x0, hx0⟩)
  refine ⟨c, C, hc, hC, ?_⟩
  intro φ hnn hφ0 hconv hφ
  obtain ⟨hm, hlin, hM⟩ := FunctionalInequalities.Probability.MomentMeasure.lintegral_nonneg_potential φ hφ hnn
  have hfinite : (∫⁻ x, (φ x).toENNReal ∂μ) ≠ ⊤ := by rw [hlin]; exact ENNReal.ofReal_ne_top
  have hvertex : ∀ x ∈ s, φ x ≤ ((C * (∫ z, (φ z).toReal ∂μ) : ℝ) : EReal) := by
    intro x hx
    have hp := hpoint ⟨x, hx⟩ φ hnn hconv.2 hm hfinite
    rw [hlin, ENNReal.toReal_ofReal hM] at hp
    exact hp.trans (EReal.coe_le_coe_iff.mpr
      (mul_le_mul_of_nonneg_right (hCle ⟨x, hx⟩) hM))
  have hfs : ∀ x ∈ s, φ x ≠ ⊤ ∧ φ x ≠ ⊥ := by
    intro x hx
    exact ⟨ne_of_lt ((hvertex x hx).trans_lt (EReal.coe_lt_top _)), hφ.1 x⟩
  have hreal : ∀ x ∈ s, (φ x).toReal ≤ C * (∫ z, (φ z).toReal ∂μ) := by
    intro x hx
    simpa only [EReal.toReal_coe] using
      EReal.toReal_le_toReal (hvertex x hx) (hφ.1 x) (EReal.coe_ne_top _)
  intro y
  refine ⟨?_, ?_⟩
  · simpa only [inner_zero_left, EReal.coe_zero, hφ0, sub_zero, FunctionalInequalities.Analysis.legendre] using
      (le_iSup (fun x : E => (inner ℝ x y : EReal) - φ x) 0)
  · exact (EReal.coe_le_coe_iff.mpr (hcoerc _ _ hreal y)).trans
      (FunctionalInequalities.Analysis.affineMaximum_le_legendre φ s hs hfs y)
