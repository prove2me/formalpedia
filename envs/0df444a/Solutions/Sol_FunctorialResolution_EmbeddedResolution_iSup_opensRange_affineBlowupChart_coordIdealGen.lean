-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.iSup_opensRange_affineBlowupChart_coordIdealGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:05:33.460922+00:00
-- url     : https://prove2.me/submissions/64d82341-cfb0-4d22-a3cf-3f7771be29db

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowup
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupUniversalLift
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupChartPreimages
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_ReesGrading
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformCharts_CoordinateBlowupChart
import Theorems.Thm_FunctorialResolution_Blowup_reesDegreeZeroEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.Blowup.reesDegreeZeroEquiv_apply


section
open CategoryTheory AlgebraicGeometry
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
universe u v
private theorem reesGenerator_mem_of_span {A : Type u} [CommRing A] (s : Set A)
    (P : Ideal ↥(reesAlgebra (Ideal.span s)))
    (hP : ∀ y ∈ s, ∀ hy : y ∈ Ideal.span s, Blowup.reesGenerator (Ideal.span s) ⟨y, hy⟩ ∈ P)
    (a : ↥(Ideal.span s)) : Blowup.reesGenerator (Ideal.span s) a ∈ P := by
  obtain ⟨r, hr⟩ := a
  induction hr using Submodule.span_induction with
  | mem x hx => exact hP x hx _
  | zero =>
      have e : Blowup.reesGenerator (Ideal.span s) (0 : ↥(Ideal.span s)) = 0 := by
        apply Subtype.ext
        simp [Blowup.reesGenerator_coe]
      show Blowup.reesGenerator (Ideal.span s) (0 : ↥(Ideal.span s)) ∈ P
      rw [e]
      exact P.zero_mem
  | add x y hx hy ihx ihy =>
      have e : Blowup.reesGenerator (Ideal.span s) ((⟨x, hx⟩ : ↥(Ideal.span s)) + ⟨y, hy⟩)
          = Blowup.reesGenerator (Ideal.span s) ⟨x, hx⟩ + Blowup.reesGenerator (Ideal.span s) ⟨y, hy⟩ := by
        apply Subtype.ext
        simp [Blowup.reesGenerator_coe]
      show Blowup.reesGenerator (Ideal.span s) ((⟨x, hx⟩ : ↥(Ideal.span s)) + ⟨y, hy⟩) ∈ P
      rw [e]
      exact P.add_mem ihx ihy
  | smul c x hx ih =>
      have e : Blowup.reesGenerator (Ideal.span s) (c • (⟨x, hx⟩ : ↥(Ideal.span s)))
          = c • Blowup.reesGenerator (Ideal.span s) ⟨x, hx⟩ := by
        apply Subtype.ext
        simp [Blowup.reesGenerator_coe, Polynomial.smul_monomial, smul_eq_mul]
      show Blowup.reesGenerator (Ideal.span s) (c • (⟨x, hx⟩ : ↥(Ideal.span s))) ∈ P
      rw [e, Algebra.smul_def]
      exact Ideal.mul_mem_left P _ ih
private theorem reesGenerator_mem_homogeneousIdeal_of_span {A : Type u} [CommRing A] (s : Set A)
    (P : HomogeneousIdeal (Blowup.reesGrading (Ideal.span s)))
    (hP : ∀ y ∈ s, ∀ hy : y ∈ Ideal.span s, Blowup.reesGenerator (Ideal.span s) ⟨y, hy⟩ ∈ P)
    (a : ↥(Ideal.span s)) : Blowup.reesGenerator (Ideal.span s) a ∈ P :=
  reesGenerator_mem_of_span s P.toIdeal (fun y hy hy2 => hP y hy hy2) a
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
universe u v
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (R : Type u) [CommRing R] {σ : Type v}
    (S : Finset σ) :
    (⨆ i : ↥S, Scheme.Hom.opensRange
        (Blowup.affineBlowupChart (coordIdeal R S) (coordIdealGen R S i.1 i.2)))
      = (⊤ : (Blowup.affineBlowup (coordIdeal R S)).Opens) := by
  refine le_antisymm le_top ?_
  rw [SetLike.le_def]
  intro x _
  have hxtop : x ∈ (⨆ a : ↥(coordIdeal R S),
      Proj.basicOpen (Blowup.reesGrading (coordIdeal R S)) (Blowup.reesGenerator (coordIdeal R S) a)) := by
    rw [Blowup.iSup_proj_basicOpen_reesGenerator_eq_top]
    trivial
  obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp hxtop
  by_contra hxn
  refine (Proj.mem_basicOpen ..).mp ha ?_
  refine reesGenerator_mem_homogeneousIdeal_of_span
    ((MvPolynomial.X : σ → MvPolynomial σ R) '' (S : Set σ)) _ ?_ a
  intro y hy hy2
  obtain ⟨i, hiS, rfl⟩ := hy
  by_contra hcon
  refine hxn (TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i, Finset.mem_coe.mp hiS⟩, ?_⟩)
  rw [Blowup.opensRange_affineBlowupChart_eq_basicOpen]
  exact (Proj.mem_basicOpen ..).mpr hcon
end FunctorialResolution.EmbeddedResolution
