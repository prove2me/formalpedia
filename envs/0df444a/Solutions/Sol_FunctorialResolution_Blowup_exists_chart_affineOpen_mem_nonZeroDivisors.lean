-- Prove2me | solution 1 for FunctorialResolution.Blowup.exists_chart_affineOpen_mem_nonZeroDivisors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:06:54.125912+00:00
-- url     : https://prove2.me/submissions/febf4438-2ba0-47c7-9468-6d11be5a03e9

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowup
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupCartier
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_ReesGrading
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupChartPreimages
import Theorems.Thm_FunctorialResolution_Blowup_sectionsRingHom_restrict
import Theorems.Thm_FunctorialResolution_Blowup_comap_specIdealSheaf_ideal
import Theorems.Thm_FunctorialResolution_Blowup_comap_specIdealSheaf_ideal_eq_span
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
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
namespace FunctorialResolution.Blowup
universe u
private theorem exists_mem_opensRange_affineBlowupChart {R : Type u} [CommRing R] (I : Ideal R)
    (p : ↥(affineBlowup I)) :
    ∃ c : ↥I, p ∈ (affineBlowupChart I c).opensRange := by
  have hcov : (⨆ c : ↥I, (affineBlowupChart I c).opensRange) = ⊤ := by
    simp only [opensRange_affineBlowupChart_eq_basicOpen]
    exact iSup_proj_basicOpen_reesGenerator_eq_top I
  have hp : p ∈ (⨆ c : ↥I, (affineBlowupChart I c).opensRange) := by
    rw [hcov]; trivial
  simpa using hp
end FunctorialResolution.Blowup
end
end

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
open FunctorialResolution FunctorialResolution.Blowup
universe u
namespace FunctorialResolution.Blowup
theorem _root_.solution {R : Type u} [CommRing R] (I : Ideal R)
    {W : Scheme.{u}} (h : W ⟶ affineBlowup I)
    (hcart : IsLocallyGeneratedByNonZeroDivisor ((specIdealSheaf I).comap (h ≫ AffineBlowup.toSpec I)))
    (w : ↥W) :
    ∃ (a : ↥I) (V : W.affineOpens), w ∈ (V : W.Opens) ∧
      (V : W.Opens) ≤ h ⁻¹ᵁ (affineBlowupChart I a ''ᵁ ⊤) ∧
      sectionsRingHom (h ≫ AffineBlowup.toSpec I) (V : W.Opens) (a : R) ∈
        nonZeroDivisors ↥Γ(W, (V : W.Opens)) := by
  obtain ⟨a, ha⟩ := exists_mem_opensRange_affineBlowupChart I (h.base w)
  have hwU₀ : w ∈ h ⁻¹ᵁ (affineBlowupChart I a ''ᵁ ⊤) := by
    have h1 := ha
    rw [← Scheme.Hom.image_top_eq_opensRange (affineBlowupChart I a)] at h1
    exact h1
  obtain ⟨U, c, hwU, hcnzd, hideal⟩ := hcart w
  have hUaff : IsAffineOpen (U : W.Opens) := U.2
  obtain ⟨t, htle, hwt⟩ :=
    hUaff.exists_basicOpen_le (V := h ⁻¹ᵁ (affineBlowupChart I a ''ᵁ ⊤)) ⟨w, hwU₀⟩ hwU
  have hwt' : w ∈ W.basicOpen t := hwt
  have : IsLocalization.Away t ↥Γ(W, W.basicOpen t) := hUaff.isLocalization_basicOpen t
  have hres : sectionsRingHom (h ≫ AffineBlowup.toSpec I) (W.basicOpen t)
      = RingHom.comp (algebraMap (↥Γ(W, (U : W.Opens))) (↥Γ(W, W.basicOpen t)))
          (sectionsRingHom (h ≫ AffineBlowup.toSpec I) (U : W.Opens)) := by
    ext r
    exact sectionsRingHom_restrict (h ≫ AffineBlowup.toSpec I) (W.basicOpen_le t) r
  have hmapU : Ideal.map (sectionsRingHom (h ≫ AffineBlowup.toSpec I) (U : W.Opens)) I
      = Ideal.span {c} := by
    rw [← comap_specIdealSheaf_ideal I (h ≫ AffineBlowup.toSpec I) U]
    exact hideal
  have hmapV : Ideal.map (sectionsRingHom (h ≫ AffineBlowup.toSpec I) (W.basicOpen t)) I
      = Ideal.span {algebraMap (↥Γ(W, (U : W.Opens))) (↥Γ(W, W.basicOpen t)) c} := by
    rw [hres, ← Ideal.map_map, hmapU, Ideal.map_span, Set.image_singleton]
  have e1 : ((specIdealSheaf I).comap (h ≫ AffineBlowup.toSpec I)).ideal
        ⟨W.basicOpen t, hUaff.basicOpen t⟩
      = Ideal.map (sectionsRingHom (h ≫ AffineBlowup.toSpec I) (W.basicOpen t)) I :=
    comap_specIdealSheaf_ideal I (h ≫ AffineBlowup.toSpec I) ⟨W.basicOpen t, hUaff.basicOpen t⟩
  have e2 : ((specIdealSheaf I).comap (h ≫ AffineBlowup.toSpec I)).ideal
        ⟨W.basicOpen t, hUaff.basicOpen t⟩
      = Ideal.span {sectionsRingHom (h ≫ AffineBlowup.toSpec I) (W.basicOpen t) (a : R)} :=
    comap_specIdealSheaf_ideal_eq_span I h a ⟨W.basicOpen t, hUaff.basicOpen t⟩ htle
  have hspan : Ideal.span {algebraMap (↥Γ(W, (U : W.Opens))) (↥Γ(W, W.basicOpen t)) c}
      = Ideal.span {sectionsRingHom (h ≫ AffineBlowup.toSpec I) (W.basicOpen t) (a : R)} :=
    hmapV.symm.trans (e1.symm.trans e2)
  have hmem2 : algebraMap (↥Γ(W, (U : W.Opens))) (↥Γ(W, W.basicOpen t)) c
      ∈ Ideal.span {sectionsRingHom (h ≫ AffineBlowup.toSpec I) (W.basicOpen t) (a : R)} := by
    rw [← hspan]
    exact Ideal.mem_span_singleton_self _
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp hmem2
  have hcnzd' : algebraMap (↥Γ(W, (U : W.Opens))) (↥Γ(W, W.basicOpen t)) c
      ∈ nonZeroDivisors ↥Γ(W, W.basicOpen t) :=
    IsLocalization.nonZeroDivisors_le_comap (Submonoid.powers t)
      ↥Γ(W, W.basicOpen t) hcnzd
  have hdnzd : d * sectionsRingHom (h ≫ AffineBlowup.toSpec I) (W.basicOpen t) (a : R)
      ∈ nonZeroDivisors ↥Γ(W, W.basicOpen t) := by
    rw [hd]
    exact hcnzd'
  exact ⟨a, ⟨W.basicOpen t, hUaff.basicOpen t⟩, hwt', htle,
    (mul_mem_nonZeroDivisors.mp hdnzd).2⟩
end FunctorialResolution.Blowup
