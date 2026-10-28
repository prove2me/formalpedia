-- Prove2me | solution 1 for FunctionalInequalities.Probability.MomentMeasure.exists_integrable_exponential_domination_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:39:19.139737+00:00
-- url     : https://prove2.me/submissions/19d135fa-1074-4eba-af02-3491d3ee18cb

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_MomentMeasure_ConjugateMass
import Theorems.Thm_FunctionalInequalities_Analysis_affineMaximum_coercive_readable
import Theorems.Thm_FunctionalInequalities_Analysis_eventually_affineMaximum_sub_le_legendre_readable
import Theorems.Thm_FunctionalInequalities_Probability_integrable_exp_sub_norm_readable

section
noncomputable section
open Filter Set
open scoped Topology
section
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

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
open FunctionalInequalities.Analysis
omit [InnerProductSpace ℝ E] in
private theorem FunctionalInequalities.Probability.MomentMeasure.density_le_exp_of_lower (ψ : E → EReal) (y : E) (c M : ℝ)
    (hlower : ((c * ‖y‖ - M : ℝ) : EReal) ≤ ψ y) :
    density ψ y ≤ ENNReal.ofReal (Real.exp (M - c * ‖y‖)) := by
  have h := EReal.exp_monotone (EReal.neg_le_neg_iff.mpr hlower)
  simpa only [density, ← EReal.coe_neg, EReal.exp_coe, neg_sub] using h
section FiniteDimensional
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
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
  obtain ⟨c, hc, hcoerc⟩ := FunctionalInequalities.Analysis.affineMaximum_coercive_readable s hs hs0
  let M : ℝ := s.sup' hs (fun x => (ψ x).toReal)
  have hMs : ∀ x ∈ s, (ψ x).toReal ≤ M := fun x hx => Finset.le_sup' (fun x => (ψ x).toReal) hx
  have hA : ∀ y, c * ‖y‖ - M ≤ FunctionalInequalities.Analysis.affineMaximum s hs (fun x => (ψ x).toReal) y :=
    hcoerc _ M hMs
  have hfs : ∀ x ∈ s, ψ x ≠ ⊤ ∧ ψ x ≠ ⊥ := fun x hx => hfin x (hsK hx)
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (FunctionalInequalities.Analysis.eventually_affineMaximum_sub_le_legendre_readable φ ψ s hs hfs
      (fun x hx => hlim x (hsK hx)) (by norm_num : (0 : ℝ) < 1))
  refine ⟨c, M + 1, N, hc, ?_, ?_, ?_⟩
  · exact (lintegral_ofReal_ne_top_iff_integrable
      (FunctionalInequalities.Probability.integrable_exp_sub_norm_readable dx hc (M + 1)).aestronglyMeasurable
      (Eventually.of_forall fun _ => (Real.exp_pos _).le)).mpr
        (FunctionalInequalities.Probability.integrable_exp_sub_norm_readable dx hc (M + 1))
  · intro y
    apply FunctionalInequalities.Probability.MomentMeasure.density_le_exp_of_lower _ y c (M + 1)
    exact (EReal.coe_le_coe_iff.mpr (by linarith [hA y])).trans
      (FunctionalInequalities.Analysis.affineMaximum_le_legendre ψ s hs hfs y)
  · intro j hj y
    apply FunctionalInequalities.Probability.MomentMeasure.density_le_exp_of_lower _ y c (M + 1)
    exact (EReal.coe_le_coe_iff.mpr (by linarith [hA y])).trans (hN j hj y)
