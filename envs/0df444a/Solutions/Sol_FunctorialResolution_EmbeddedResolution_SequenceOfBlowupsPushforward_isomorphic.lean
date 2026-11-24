-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.SequenceOfBlowupsPushforward.isomorphic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:01:30.918113+00:00
-- url     : https://prove2.me/submissions/c7bbc890-1a22-4dbc-9111-bd0a660fdebe

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_ClosedEmbedding_StrictTransformClosedImmersion
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_ClosedEmbedding_PushforwardUniqueness
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowupsPushforward_length_eq_length
import Theorems.Thm_FunctorialResolution_Blowup_comap_map_of_isClosedImmersion
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_isBlowupAlongIdealSheaf_blowupMorphism
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_imageIdealSheaf_comp
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_map_eq_imageIdealSheaf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
private theorem comap_imageIdealSheaf_of_isIso {A B : Scheme.{u}} (f : A ⟶ B) [IsIso f]
    (J : A.IdealSheafData) :
    (imageIdealSheaf f J).comap f = J := by
  rw [show imageIdealSheaf f J = J.map f from map_eq_imageIdealSheaf ..]
  exact Blowup.comap_map_of_isClosedImmersion f J
private theorem exists_iso_succ_comp_blowupMorphism {X : Scheme.{u}} (B B' : SequenceOfBlowups X) (i : ℕ)
    (hi : i < B.length) (hi' : i < B'.length) (f : B.schemeAt i ≅ B'.schemeAt i)
    (hf : (B'.center i).comap f.hom = B.center i) :
    ∃ g : B.schemeAt (i + 1) ≅ B'.schemeAt (i + 1),
      g.hom ≫ B'.transitionMapSucc i = B.transitionMapSucc i ≫ f.hom := by
  have hB := B.isBlowupAlongIdealSheaf_blowupMorphism i hi
  have hB' := B'.isBlowupAlongIdealSheaf_blowupMorphism i hi'
  have cB : Blowup.IsLocallyGeneratedByNonZeroDivisor ((B.center i).comap (B.transitionMapSucc i)) := hB.1
  have cB' : Blowup.IsLocallyGeneratedByNonZeroDivisor ((B'.center i).comap (B'.transitionMapSucc i)) := hB'.1
  have hinv : (B.center i).comap f.inv = B'.center i := by
    rw [← hf, ← AlgebraicGeometry.Scheme.IdealSheafData.comap_comp, Iso.inv_hom_id,
      AlgebraicGeometry.Scheme.IdealSheafData.comap_id]
  have c1 : Blowup.IsLocallyGeneratedByNonZeroDivisor ((B'.center i).comap (B.transitionMapSucc i ≫ f.hom)) := by
    rw [AlgebraicGeometry.Scheme.IdealSheafData.comap_comp, hf]
    exact cB
  have c2 : Blowup.IsLocallyGeneratedByNonZeroDivisor ((B.center i).comap (B'.transitionMapSucc i ≫ f.inv)) := by
    rw [AlgebraicGeometry.Scheme.IdealSheafData.comap_comp, hinv]
    exact cB'
  obtain ⟨a, ha⟩ := (hB'.2 _ (B.transitionMapSucc i ≫ f.hom) c1).exists
  obtain ⟨b, hb⟩ := (hB.2 _ (B'.transitionMapSucc i ≫ f.inv) c2).exists
  have hab : a ≫ b = 𝟙 _ := by
    refine (hB.2 _ (B.transitionMapSucc i) cB).unique ?_ ?_
    · rw [Category.assoc, hb, ← Category.assoc, ha, Category.assoc, Iso.hom_inv_id,
        Category.comp_id]
    · rw [Category.id_comp]
  have hba : b ≫ a = 𝟙 _ := by
    refine (hB'.2 _ (B'.transitionMapSucc i) cB').unique ?_ ?_
    · rw [Category.assoc, ha, ← Category.assoc, hb, Category.assoc, Iso.inv_hom_id,
        Category.comp_id]
    · rw [Category.id_comp]
  exact ⟨⟨a, b, hab, hba⟩, ha⟩
private theorem comap_center_eq_of_sequenceOfBlowupsPushforward {S X : Scheme.{u}} {j : S ⟶ X}
    {BS : SequenceOfBlowups S} {B B' : SequenceOfBlowups X}
    (d : SequenceOfBlowupsPushforward j BS B) (d' : SequenceOfBlowupsPushforward j BS B')
    (i : ℕ) (hi : i < B.length) (hi' : i < B'.length)
    (f : B.schemeAt i ≅ B'.schemeAt i) (hf : d.σ i hi.le ≫ f.hom = d'.σ i hi'.le) :
    (B'.center i).comap f.hom = B.center i := by
  rw [d'.center i hi', ← hf, imageIdealSheaf_comp, comap_imageIdealSheaf_of_isIso, d.center i hi]
namespace SequenceOfBlowupsPushforward
end SequenceOfBlowupsPushforward
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.SequenceOfBlowupsPushforward
namespace FunctorialResolution.EmbeddedResolution.SequenceOfBlowupsPushforward
theorem _root_.solution {S X : Scheme.{u}} {j : S ⟶ X} [IsClosedImmersion j]
    {BS : SequenceOfBlowups S} {B B' : SequenceOfBlowups X}
    (d : SequenceOfBlowupsPushforward j BS B) (d' : SequenceOfBlowupsPushforward j BS B') :
    B.Isomorphic B' := by
  have hlength : B.length = B'.length := length_eq_length d d'
  have hSL : BS.length = B.length := d.lengthEq
  have key : ∀ n : ℕ, n ≤ B.length →
      ∃ e : ∀ i : ℕ, i ≤ n → (B.schemeAt i ≅ B'.schemeAt i),
        (∀ (i : ℕ) (hi : i ≤ n) (h1 : i ≤ B.length) (h2 : i ≤ B'.length),
            d.σ i h1 ≫ (e i hi).hom = d'.σ i h2) ∧
        ((e 0 (Nat.zero_le n)).hom ≫ B'.isoZero.hom = B.isoZero.hom) ∧
        (∀ (i : ℕ) (hi : i + 1 ≤ n),
            (e (i + 1) hi).hom ≫ B'.transitionMapSucc i
              = B.transitionMapSucc i ≫ (e i (Nat.le_of_succ_le hi)).hom) := by
    intro n
    induction n with
    | zero =>
        intro _
        refine ⟨fun i hi => eqToIso (congrArg B.schemeAt (Nat.le_zero.mp hi)) ≪≫
          (B.isoZero ≪≫ B'.isoZero.symm) ≪≫
          eqToIso (congrArg B'.schemeAt (Nat.le_zero.mp hi).symm), ?_, ?_, ?_⟩
        · intro i hi h1 h2
          obtain rfl : i = 0 := Nat.le_zero.mp hi
          have hz : d.σ 0 h1 ≫ B.isoZero.hom = d'.σ 0 h2 ≫ B'.isoZero.hom :=
            d.zero.trans d'.zero.symm
          have hgoal : d.σ 0 h1 ≫ B.isoZero.hom ≫ B'.isoZero.inv = d'.σ 0 h2 := by
            rw [← Category.assoc, hz, Category.assoc, Iso.hom_inv_id, Category.comp_id]
          simpa using hgoal
        · simp
        · intro i hi
          exact absurd hi (Nat.not_succ_le_zero i)
    | succ n ih =>
        intro hn1
        obtain ⟨e, hσ, h0, hsq⟩ := ih (by omega)
        have hnB : n < B.length := by omega
        have hnB' : n < B'.length := by omega
        have hnS : n < BS.length := by omega
        have hcen : (B'.center n).comap (e n le_rfl).hom = B.center n :=
          comap_center_eq_of_sequenceOfBlowupsPushforward d d' n hnB hnB' (e n le_rfl)
            (hσ n le_rfl hnB.le hnB'.le)
        obtain ⟨g, hg⟩ := exists_iso_succ_comp_blowupMorphism B B' n hnB hnB' (e n le_rfl) hcen
        refine ⟨fun i hi => if hin : i ≤ n then e i hin else
            eqToIso (congrArg B.schemeAt (by omega : i = n + 1)) ≪≫ g ≪≫
              eqToIso (congrArg B'.schemeAt (by omega : n + 1 = i)), ?_, ?_, ?_⟩
        · intro i hi h1 h2
          by_cases hin : i ≤ n
          · simp only [dif_pos hin]
            exact hσ i hin h1 h2
          · have hie : i = n + 1 := by omega
            subst hie
            simp only [dif_neg hin, Iso.trans_hom, eqToIso.hom, eqToHom_refl,
              Category.id_comp, Category.comp_id]
            have hBcen : (B'.center n).comap (d'.σ n hnB'.le) = BS.center n := by
              have := d'.isClosedImmersion n hnB'.le
              rw [d'.center n hnB', show imageIdealSheaf (d'.σ n hnB'.le) (BS.center n)
                  = (BS.center n).map (d'.σ n hnB'.le) from map_eq_imageIdealSheaf ..,
                Blowup.comap_map_of_isClosedImmersion]
            have hcart : Blowup.IsLocallyGeneratedByNonZeroDivisor
                ((B'.center n).comap (BS.transitionMapSucc n ≫ d'.σ n hnB'.le)) := by
              rw [AlgebraicGeometry.Scheme.IdealSheafData.comap_comp, hBcen]
              exact (BS.isBlowupAlongIdealSheaf_blowupMorphism n hnS).1
            have hstep : (d.σ (n + 1) hnB ≫ g.hom) ≫ B'.transitionMapSucc n
                = BS.transitionMapSucc n ≫ d'.σ n hnB'.le := by
              rw [Category.assoc, hg, ← Category.assoc, d.square n hnB, Category.assoc,
                hσ n le_rfl hnB.le hnB'.le]
            exact ((B'.isBlowupAlongIdealSheaf_blowupMorphism n hnB').2 _
              (BS.transitionMapSucc n ≫ d'.σ n hnB'.le) hcart).unique hstep (d'.square n hnB')
        · have hzz : (0 : ℕ) ≤ n := Nat.zero_le n
          simp only [dif_pos hzz]
          exact h0
        · intro i hi
          by_cases hin : i + 1 ≤ n
          · have hin' : i ≤ n := Nat.le_of_succ_le hin
            simp only [dif_pos hin, dif_pos hin']
            exact hsq i hin
          · have hien : i = n := by omega
            have hile : i ≤ n := le_of_eq hien
            subst hien
            simp only [dif_neg hin, dif_pos hile, Iso.trans_hom, eqToIso.hom, eqToHom_refl,
              Category.id_comp, Category.comp_id]
            exact hg
  obtain ⟨e, hσ, h0, hsq⟩ := key B.length le_rfl
  refine ⟨hlength, e, h0, ?_, ?_⟩
  · intro i hi
    exact hsq i hi
  · intro i hi
    exact comap_center_eq_of_sequenceOfBlowupsPushforward d d' i hi (by omega) (e i hi.le)
      (hσ i hi.le hi.le (by omega))
end FunctorialResolution.EmbeddedResolution.SequenceOfBlowupsPushforward
