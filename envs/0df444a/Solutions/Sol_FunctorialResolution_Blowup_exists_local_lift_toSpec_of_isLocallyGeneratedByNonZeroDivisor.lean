-- Prove2me | solution 1 for FunctorialResolution.Blowup.exists_local_lift_toSpec_of_isLocallyGeneratedByNonZeroDivisor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:33:43.851037+00:00
-- url     : https://prove2.me/submissions/881fd102-3f3f-4ea4-ac61-ddb31ec5e7ec

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowup
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupCartier
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupUniversalLift
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupOpenCover
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupChartPreimages
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupUniversal
import Theorems.Thm_FunctorialResolution_Blowup_comap_specIdealSheaf_ideal
import Theorems.Thm_FunctorialResolution_Blowup_exists_lift_affineBlowup
import Theorems.Thm_FunctorialResolution_Blowup_globalSectionsRingHom_eq
import Theorems.Thm_FunctorialResolution_Blowup_map_mem_nonZeroDivisors_of_iso
import Theorems.Thm_FunctorialResolution_Blowup_reesDegreeZeroEquiv_apply
import Theorems.Thm_FunctorialResolution_Blowup_sectionsRingHom_apply
import Theorems.Thm_FunctorialResolution_Blowup_sectionsRingHom_restrict
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
namespace FunctorialResolution.Blowup
universe u
private theorem exists_sum_mul_eq_one_of_map_eq_span {R A : Type u} [CommRing R] [CommRing A]
    (I : Ideal R) (φ : R →+* A) (s : A) (hmap : Ideal.map φ I = Ideal.span {s})
    (hs : s ∈ nonZeroDivisors A) :
    ∃ (n : ℕ) (a : Fin n → ↥I) (c d : Fin n → A),
      (∀ i, φ (a i : R) = d i * s) ∧ ∑ i, c i * d i = 1 := by
  have hsmem : s ∈ Ideal.map φ I := by
    rw [hmap]; exact Ideal.subset_span rfl
  rw [← Ideal.span_eq I, Ideal.map_span] at hsmem
  obtain ⟨n, c, gg, hsum⟩ := Submodule.mem_span_set'.mp hsmem
  choose a ha hφa using fun i => (gg i).2
  have hdex : ∀ i, ∃ e : A, φ (a i) = e * s := by
    intro i
    have hmem : φ (a i) ∈ Ideal.span {s} := by
      rw [← hmap]
      exact Ideal.mem_map_of_mem _ (ha i)
    obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.mp hmem
    exact ⟨e, he.symm⟩
  choose d hdd using hdex
  refine ⟨n, fun i => ⟨a i, ha i⟩, c, d, fun i => hdd i, ?_⟩
  have hss : (∑ i, c i * d i) * s = s := by
    rw [Finset.sum_mul]
    conv_rhs => rw [← hsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, ← hφa i, hdd i, mul_assoc]
  have h1 : ((∑ i, c i * d i) - 1) * s = 0 := by
    rw [sub_mul, hss, one_mul, sub_self]
  have h2 := mem_nonZeroDivisors_iff_right.mp hs _ h1
  linear_combination h2
private theorem exists_mem_basicOpen_of_sum_mul_eq_one {X : Scheme.{u}} {V : X.Opens} {n : ℕ}
    (c d : Fin n → ↥Γ(X, V)) (hsum : ∑ i, c i * d i = 1) (w : ↥X) (hw : w ∈ V) :
    ∃ i, w ∈ X.basicOpen (d i) := by
  by_contra hcon
  push Not at hcon
  have hmem : ∀ i, (X.presheaf.germ V w hw).hom (d i)
      ∈ IsLocalRing.maximalIdeal ↥(X.presheaf.stalk w) := by
    intro i
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact hcon i ((X.mem_basicOpen (d i) w hw).mpr hu)
  have h1 : (1 : ↥(X.presheaf.stalk w)) ∈ IsLocalRing.maximalIdeal ↥(X.presheaf.stalk w) := by
    have hone : (X.presheaf.germ V w hw).hom (1 : ↥Γ(X, V)) = 1 := map_one _
    rw [← hone, ← hsum, map_sum]
    refine Ideal.sum_mem _ fun i _ => ?_
    rw [map_mul]
    exact Ideal.mul_mem_left _ _ (hmem i)
  exact (IsLocalRing.maximalIdeal.isMaximal ↥(X.presheaf.stalk w)).ne_top
    ((Ideal.eq_top_iff_one _).mpr h1)
private theorem appLE_top_top_eq_appTop {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : (⊤ : X.Opens) ≤ f ⁻¹ᵁ (⊤ : Y.Opens)) : f.appLE ⊤ ⊤ h = f.appTop := by
  have h2 : X.presheaf.map (homOfLE h).op = 𝟙 _ :=
    CategoryTheory.Functor.map_id _ _
  simp only [Scheme.Hom.appLE, h2]
  rfl
private theorem appLE_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Z.Opens)
    (V : Y.Opens) (V' : X.Opens) (e₁ : V ≤ g ⁻¹ᵁ U) (e₂ : V' ≤ f ⁻¹ᵁ V)
    (e : V' ≤ (f ≫ g) ⁻¹ᵁ U) :
    (f ≫ g).appLE U V' e = g.appLE U V e₁ ≫ f.appLE V V' e₂ := by
  rw [Scheme.Hom.appLE_comp_appLE]
private theorem isIso_ι_appLE {W : Scheme.{u}} (U : W.Opens)
    (hle : (⊤ : U.toScheme.Opens) ≤ U.ι ⁻¹ᵁ U) : IsIso (U.ι.appLE U ⊤ hle) := by
  have h1 : U.ι ''ᵁ (⊤ : U.toScheme.Opens) = U := by simp
  have h2 : U.ι.appLE U ⊤ hle
      = W.presheaf.map (eqToHom h1).op ≫ (U.ι.appIso ⊤).hom := by
    rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]
  rw [h2, eqToHom_op, eqToHom_map]
  infer_instance
private theorem appTop_ι_comp_eq_appLE_comp {R : Type u} [CommRing R] {W : Scheme.{u}} (U : W.Opens)
    (g : W ⟶ Spec (CommRingCat.of R)) (hle : (⊤ : U.toScheme.Opens) ≤ U.ι ⁻¹ᵁ U)
    (hle' : U ≤ g ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of R)).Opens)) :
    (U.ι ≫ g).appTop = g.appLE ⊤ U hle' ≫ U.ι.appLE U ⊤ hle := by
  rw [← appLE_top_top_eq_appTop (U.ι ≫ g) (by simp)]
  exact appLE_comp U.ι g ⊤ U ⊤ hle' hle (by simp)
private theorem exists_sections_iso_globalSectionsRingHom {R : Type u} [CommRing R] {W : Scheme.{u}} (U : W.Opens)
    (g : W ⟶ Spec (CommRingCat.of R)) :
    ∃ e : Γ(W, U) ≅ Γ(U.toScheme, ⊤),
      ∀ r : R, globalSectionsRingHom (U.ι ≫ g) r
        = (CommRingCat.Hom.hom e.hom) (sectionsRingHom g U r) := by
  have hle : (⊤ : U.toScheme.Opens) ≤ U.ι ⁻¹ᵁ U := by simp
  have hle' : U ≤ g ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of R)).Opens) := by simp
  have := isIso_ι_appLE U hle
  refine ⟨asIso (U.ι.appLE U ⊤ hle), fun r => ?_⟩
  have hcomp := appTop_ι_comp_eq_appLE_comp U g hle hle'
  simp only [globalSectionsRingHom_eq, hcomp, asIso_hom, CommRingCat.hom_comp, RingHom.comp_apply,
    sectionsRingHom_apply]
end FunctorialResolution.Blowup
end
end

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.Blowup
universe u
namespace FunctorialResolution.Blowup
theorem _root_.solution {R : Type u} [CommRing R] (I : Ideal R)
    {W : Scheme.{u}} (g : W ⟶ Spec (CommRingCat.of R))
    (hcart : IsLocallyGeneratedByNonZeroDivisor ((specIdealSheaf I).comap g)) (w : ↥W) :
    ∃ (U : W.Opens) (_ : w ∈ U) (h : U.toScheme ⟶ affineBlowup I),
      h ≫ AffineBlowup.toSpec I = U.ι ≫ g := by
  obtain ⟨V, s, hwV, hs, hspan⟩ := hcart w
  have hmap : Ideal.map (sectionsRingHom g (V : W.Opens)) I = Ideal.span {s} :=
    (comap_specIdealSheaf_ideal I g V).symm.trans hspan
  obtain ⟨n, a, c, d, hd, hsum⟩ :=
    exists_sum_mul_eq_one_of_map_eq_span I (sectionsRingHom g (V : W.Opens)) s hmap hs
  obtain ⟨i, hi⟩ := exists_mem_basicOpen_of_sum_mul_eq_one c d hsum w hwV
  have hLoc : IsLocalization.Away (d i) ↥Γ(W, W.basicOpen (d i)) :=
    V.2.isLocalization_basicOpen (d i)
  have hUV : W.basicOpen (d i) ≤ (V : W.Opens) := W.basicOpen_le (d i)
  have : IsAffine (W.basicOpen (d i)).toScheme := V.2.basicOpen (d i)
  have hunit : IsUnit ((W.presheaf.map (homOfLE hUV).op).hom (d i)) :=
    IsLocalization.map_units (M := Submonoid.powers (d i)) _ ⟨d i, Submonoid.mem_powers _⟩
  have hrs : (W.presheaf.map (homOfLE hUV).op).hom s
      ∈ nonZeroDivisors ↥Γ(W, W.basicOpen (d i)) :=
    IsLocalization.nonZeroDivisors_le_comap (Submonoid.powers (d i)) _ hs
  have hres : ∀ r : R, sectionsRingHom g (W.basicOpen (d i)) r
      = (W.presheaf.map (homOfLE hUV).op).hom (sectionsRingHom g (V : W.Opens) r) :=
    fun r => sectionsRingHom_restrict g hUV r
  have hcomp : sectionsRingHom g (W.basicOpen (d i))
      = (W.presheaf.map (homOfLE hUV).op).hom.comp (sectionsRingHom g (V : W.Opens)) :=
    RingHom.ext hres
  have hmapSpan : Ideal.map (sectionsRingHom g (W.basicOpen (d i))) I
      = Ideal.span {sectionsRingHom g (W.basicOpen (d i)) (a i : R)} := by
    have h1 : Ideal.map (sectionsRingHom g (W.basicOpen (d i))) I
        = Ideal.span {(W.presheaf.map (homOfLE hUV).op).hom (d i)
            * (W.presheaf.map (homOfLE hUV).op).hom s} := by
      rw [hcomp, ← Ideal.map_map, hmap, Ideal.map_span, Set.image_singleton]
      exact (Ideal.span_singleton_mul_left_unit hunit _).symm
    rw [h1, hres (a i : R), hd i, map_mul]
  have hnonZeroDivU : sectionsRingHom g (W.basicOpen (d i)) (a i : R)
      ∈ nonZeroDivisors ↥Γ(W, W.basicOpen (d i)) := by
    rw [hres, hd i, map_mul]
    exact mul_mem hunit.mem_nonZeroDivisors hrs
  obtain ⟨e, he⟩ := exists_sections_iso_globalSectionsRingHom (W.basicOpen (d i)) g
  have hgen' : Ideal.map (globalSectionsRingHom ((W.basicOpen (d i)).ι ≫ g)) I
      = Ideal.span {globalSectionsRingHom ((W.basicOpen (d i)).ι ≫ g) (a i : R)} := by
    have e1 : Ideal.map (globalSectionsRingHom ((W.basicOpen (d i)).ι ≫ g)) I
        = Ideal.map (CommRingCat.Hom.hom e.hom)
            (Ideal.map (sectionsRingHom g (W.basicOpen (d i))) I) := by
      rw [Ideal.map_map]
      exact congrArg (fun ϕ => Ideal.map ϕ I) (RingHom.ext he)
    rw [e1, hmapSpan, Ideal.map_span, Set.image_singleton, he]
  have hnonZeroDiv' : globalSectionsRingHom ((W.basicOpen (d i)).ι ≫ g) (a i : R)
      ∈ nonZeroDivisors ↥Γ((W.basicOpen (d i)).toScheme, ⊤) := by
    rw [he]
    exact map_mem_nonZeroDivisors_of_iso e hnonZeroDivU
  obtain ⟨h, hh, -⟩ :=
    exists_lift_affineBlowup I ((W.basicOpen (d i)).ι ≫ g) (a i) hgen' hnonZeroDiv'
  exact ⟨W.basicOpen (d i), hi, h, hh⟩
end FunctorialResolution.Blowup
