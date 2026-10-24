-- Prove2me | solution 1 for FunctionalInequalities.Probability.MomentMeasure.exists_integrable_exponential_domination_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:28:38.492623+00:00
-- url     : https://prove2.me/submissions/f7d0fd67-9c76-4dc4-adba-541de0097ba2

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
import Theorems.Thm_FunctionalInequalities_Analysis_affineMaximum_coercive_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_eventually_affineMaximum_sub_le_legendre_408915f
import Theorems.Thm_FunctionalInequalities_Probability_integrable_exp_sub_norm_408915f

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
omit [InnerProductSpace ℝ E] in
private theorem FunctionalInequalities.Probability.MomentMeasure.density_le_exp_of_lower (ψ : E → EReal) (y : E) (c M : ℝ)
    (hlower : ((c * ‖y‖ - M : ℝ) : EReal) ≤ ψ y) :
    density ψ y ≤ ENNReal.ofReal (Real.exp (M - c * ‖y‖)) := by
  have h := EReal.exp_monotone (EReal.neg_le_neg_iff.mpr hlower)
  simpa only [density, ← EReal.coe_neg, EReal.exp_coe, neg_sub] using h
section FiniteDimensional
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
namespace FunctionalInequalities.Probability.MomentMeasure
end FunctionalInequalities.Probability.MomentMeasure
open FunctionalInequalities.Probability.MomentMeasure in
/-- The original open-neighborhood geometry and vertex convergence produce the
actual common exponential dominator. Finiteness is proved rather than supplied.
No condition on initial dual masses is used, and zero-dimensional Haar is included. -/
theorem solution
    (dx : Measure E) [dx.IsAddHaarMeasure]
    (φ : ℕ → E → EReal) (ψ : E → EReal) {K : Set E}
    (hK : IsOpen K) (h0 : (0 : E) ∈ K)
    (hfin : ∀ x ∈ K, ψ x ≠ ⊤ ∧ ψ x ≠ ⊥)
    (hlim : ∀ x ∈ K, Tendsto (fun j => φ j x) atTop (𝓝 (ψ x))) :
    ∃ (c M : ℝ) (N : ℕ), 0 < c ∧
      (∫⁻ y, ENNReal.ofReal (Real.exp (M - c * ‖y‖)) ∂dx) ≠ ⊤ ∧
      (∀ y, FunctionalInequalities.Probability.MomentMeasure.density (FunctionalInequalities.Analysis.legendre ψ) y ≤ ENNReal.ofReal (Real.exp (M - c * ‖y‖))) ∧
      ∀ j, N ≤ j → ∀ y,
        FunctionalInequalities.Probability.MomentMeasure.density (FunctionalInequalities.Analysis.legendre (φ j)) y ≤ ENNReal.ofReal (Real.exp (M - c * ‖y‖)) := by
  classical
  obtain ⟨s, hs, hsK, hs0⟩ := FunctionalInequalities.Analysis.exists_finite_hull_neighborhood hK h0
  obtain ⟨c, hc, hcoerc⟩ := FunctionalInequalities.Analysis.affineMaximum_coercive_408915f s hs hs0
  let M : ℝ := s.sup' hs (fun x => (ψ x).toReal)
  have hMs : ∀ x ∈ s, (ψ x).toReal ≤ M := fun x hx => Finset.le_sup' (fun x => (ψ x).toReal) hx
  have hA : ∀ y, c * ‖y‖ - M ≤ FunctionalInequalities.Analysis.affineMaximum s hs (fun x => (ψ x).toReal) y :=
    hcoerc _ M hMs
  have hfs : ∀ x ∈ s, ψ x ≠ ⊤ ∧ ψ x ≠ ⊥ := fun x hx => hfin x (hsK hx)
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (FunctionalInequalities.Analysis.eventually_affineMaximum_sub_le_legendre_408915f φ ψ s hs hfs
      (fun x hx => hlim x (hsK hx)) (by norm_num : (0 : ℝ) < 1))
  refine ⟨c, M + 1, N, hc, ?_, ?_, ?_⟩
  · exact (lintegral_ofReal_ne_top_iff_integrable
      (FunctionalInequalities.Probability.integrable_exp_sub_norm_408915f dx hc (M + 1)).aestronglyMeasurable
      (Eventually.of_forall fun _ => (Real.exp_pos _).le)).mpr
        (FunctionalInequalities.Probability.integrable_exp_sub_norm_408915f dx hc (M + 1))
  · intro y
    apply density_le_exp_of_lower _ y c (M + 1)
    exact (EReal.coe_le_coe_iff.mpr (by linarith [hA y])).trans
      (FunctionalInequalities.Analysis.affineMaximum_le_legendre ψ s hs hfs y)
  · intro j hj y
    apply density_le_exp_of_lower _ y c (M + 1)
    exact (EReal.coe_le_coe_iff.mpr (by linarith [hA y])).trans (hN j hj y)
