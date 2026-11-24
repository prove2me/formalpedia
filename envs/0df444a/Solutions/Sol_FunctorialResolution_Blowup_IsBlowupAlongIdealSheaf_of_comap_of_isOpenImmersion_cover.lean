-- Prove2me | solution 1 for FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf.of_comap_of_isOpenImmersion_cover
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:27:36.574752+00:00
-- url     : https://prove2.me/submissions/c2e3c7e6-2978-432b-80c4-a864e28df3f5

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupOpenCover
import Theorems.Thm_FunctorialResolution_Blowup_IsLocallyGeneratedByNonZeroDivisor_comap_of_isOpenImmersion
import Theorems.Thm_FunctorialResolution_Blowup_IsLocallyGeneratedByNonZeroDivisor_of_isOpenImmersion_cover
import Theorems.Thm_FunctorialResolution_Blowup_IsBlowupAlongIdealSheaf_hom_ext_of_comp_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u v
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite
namespace FunctorialResolution.Blowup
private theorem hom_ext_of_isOpenImmersion_cover {X W T : Scheme.{u}} {ι : Type v}
    (U : ι → Scheme.{u}) (f : ∀ i, U i ⟶ X) [∀ i, IsOpenImmersion (f i)]
    (hcover : ∀ x : X, ∃ i, x ∈ Set.range ⇑(f i).base) (g : W ⟶ X) {a b : W ⟶ T}
    (h : ∀ i, pullback.fst g (f i) ≫ a = pullback.fst g (f i) ≫ b) : a = b := by
  refine Scheme.Cover.hom_ext (pullbackOpenCoverOfCovers U f hcover g) a b (fun i => ?_)
  exact h i
private theorem exists_hom_of_isOpenImmersion_cover {X W T : Scheme.{u}} {ι : Type v}
    (U : ι → Scheme.{u}) (f : ∀ i, U i ⟶ X) [∀ i, IsOpenImmersion (f i)]
    (hcover : ∀ x : X, ∃ i, x ∈ Set.range ⇑(f i).base) (g : W ⟶ X)
    (k : ∀ i, pullback g (f i) ⟶ T)
    (hk : ∀ i j, pullback.fst (pullback.fst g (f i)) (pullback.fst g (f j)) ≫ k i
        = pullback.snd (pullback.fst g (f i)) (pullback.fst g (f j)) ≫ k j) :
    ∃ φ : W ⟶ T, ∀ i, pullback.fst g (f i) ≫ φ = k i := by
  have hk' : ∀ i j,
      pullback.fst ((pullbackOpenCoverOfCovers U f hcover g).f i) ((pullbackOpenCoverOfCovers U f hcover g).f j) ≫ k i
        = pullback.snd ((pullbackOpenCoverOfCovers U f hcover g).f i)
            ((pullbackOpenCoverOfCovers U f hcover g).f j) ≫ k j :=
    fun i j => hk i j
  refine ⟨Scheme.Cover.glueMorphisms (pullbackOpenCoverOfCovers U f hcover g) k hk', fun i => ?_⟩
  exact Scheme.Cover.ι_glueMorphisms (pullbackOpenCoverOfCovers U f hcover g) k hk' i
private theorem eq_of_comp_eq_of_isBlowupAlongIdealSheaf_openCover {X X' T : Scheme.{u}} (π : X' ⟶ X)
    (I : X.IdealSheafData)
    {ι : Type v} (U : ι → Scheme.{u}) (f : ∀ i, U i ⟶ X) [∀ i, IsOpenImmersion (f i)]
    (hcover : ∀ x : X, ∃ i, x ∈ Set.range ⇑(f i).base)
    (h : ∀ i, IsBlowupAlongIdealSheaf (pullback.snd π (f i)) (I.comap (f i)))
    {a b : T ⟶ X'} (hab : a ≫ π = b ≫ π) (hc : IsLocallyGeneratedByNonZeroDivisor (I.comap (a ≫ π))) :
    a = b := by
  refine hom_ext_of_isOpenImmersion_cover U f hcover (a ≫ π) fun i => ?_
  have hcond : pullback.fst (a ≫ π) (f i) ≫ (a ≫ π) = pullback.snd (a ≫ π) (f i) ≫ f i :=
    pullback.condition
  have ha' : (pullback.fst (a ≫ π) (f i) ≫ a) ≫ π = pullback.snd (a ≫ π) (f i) ≫ f i := by
    rw [Category.assoc]; exact hcond
  have hb' : (pullback.fst (a ≫ π) (f i) ≫ b) ≫ π = pullback.snd (a ≫ π) (f i) ≫ f i := by
    rw [Category.assoc, ← hab]; exact hcond
  have hEC : IsLocallyGeneratedByNonZeroDivisor ((I.comap (f i)).comap (pullback.snd (a ≫ π) (f i))) := by
    rw [← Scheme.IdealSheafData.comap_comp, ← hcond, Scheme.IdealSheafData.comap_comp]
    exact hc.comap_of_isOpenImmersion _
  have hAB := (h i).hom_ext_of_comp_eq hEC
    (pullback.lift_snd (pullback.fst (a ≫ π) (f i) ≫ a) (pullback.snd (a ≫ π) (f i)) ha')
    (pullback.lift_snd (pullback.fst (a ≫ π) (f i) ≫ b) (pullback.snd (a ≫ π) (f i)) hb')
  have h1 := pullback.lift_fst (pullback.fst (a ≫ π) (f i) ≫ a) (pullback.snd (a ≫ π) (f i)) ha'
  have h2 := pullback.lift_fst (pullback.fst (a ≫ π) (f i) ≫ b) (pullback.snd (a ≫ π) (f i)) hb'
  rw [← h1, ← h2, hAB]
end FunctorialResolution.Blowup
end

set_option autoImplicit false
universe u v
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite
open FunctorialResolution FunctorialResolution.Blowup
namespace FunctorialResolution.Blowup
namespace IsBlowupAlongIdealSheaf
theorem _root_.solution {X X' : Scheme.{u}} (π : X' ⟶ X)
    (I : X.IdealSheafData) {ι : Type v} (U : ι → Scheme.{u}) (f : ∀ i, U i ⟶ X)
    [∀ i, IsOpenImmersion (f i)]
    (hcover : ∀ x : X, ∃ i, x ∈ Set.range ⇑(f i).base)
    (h : ∀ i, IsBlowupAlongIdealSheaf (pullback.snd π (f i)) (I.comap (f i))) :
    IsBlowupAlongIdealSheaf π I := by
  constructor
  · refine IsLocallyGeneratedByNonZeroDivisor.of_isOpenImmersion_cover (I.comap π) (fun i => pullback π (f i))
      (fun i => pullback.fst π (f i)) (fun x' => ?_) ?_
    · obtain ⟨i, hi⟩ := hcover (π.base x')
      obtain ⟨z, hz⟩ := exists_pullback_fst_base_eq π (f i) x' hi
      exact ⟨i, z, hz⟩
    · intro i
      have hq : (I.comap π).comap (pullback.fst π (f i))
          = (I.comap (f i)).comap (pullback.snd π (f i)) := by
        rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
          pullback.condition]
      rw [hq]
      exact (h i).1
  · intro W g hg
    have hEC : ∀ i, IsLocallyGeneratedByNonZeroDivisor ((I.comap (f i)).comap (pullback.snd g (f i))) := by
      intro i
      have hq : (I.comap (f i)).comap (pullback.snd g (f i))
          = (I.comap g).comap (pullback.fst g (f i)) := by
        rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
          pullback.condition]
      rw [hq]
      exact hg.comap_of_isOpenImmersion _
    choose k hk1 _ using fun i => (h i).2 (pullback g (f i)) (pullback.snd g (f i)) (hEC i)
    have hapi : ∀ i, k i ≫ pullback.fst π (f i) ≫ π = pullback.fst g (f i) ≫ g := by
      intro i
      rw [pullback.condition, ← Category.assoc, hk1 i, ← pullback.condition]
    have hglue : ∀ i j, pullback.fst (pullback.fst g (f i)) (pullback.fst g (f j)) ≫
          (k i ≫ pullback.fst π (f i))
        = pullback.snd (pullback.fst g (f i)) (pullback.fst g (f j)) ≫
          (k j ≫ pullback.fst π (f j)) := by
      intro i j
      refine eq_of_comp_eq_of_isBlowupAlongIdealSheaf_openCover π I U f hcover h ?_ ?_
      · simp only [Category.assoc]
        rw [hapi i, hapi j, ← Category.assoc, ← Category.assoc, pullback.condition]
      · have heq : (pullback.fst (pullback.fst g (f i)) (pullback.fst g (f j)) ≫
              (k i ≫ pullback.fst π (f i))) ≫ π
            = (pullback.fst (pullback.fst g (f i)) (pullback.fst g (f j)) ≫
              pullback.fst g (f i)) ≫ g := by
          rw [Category.assoc, Category.assoc, hapi i, ← Category.assoc]
        rw [heq, Scheme.IdealSheafData.comap_comp]
        exact hg.comap_of_isOpenImmersion _
    obtain ⟨φ, hφ⟩ :=
      exists_hom_of_isOpenImmersion_cover U f hcover g
        (fun i => k i ≫ pullback.fst π (f i)) hglue
    have hφπ : φ ≫ π = g := by
      refine hom_ext_of_isOpenImmersion_cover U f hcover g fun i => ?_
      rw [← Category.assoc, hφ i, Category.assoc, hapi i]
    refine ⟨φ, hφπ, fun y hy => ?_⟩
    have hy' : y ≫ π = g := hy
    refine eq_of_comp_eq_of_isBlowupAlongIdealSheaf_openCover π I U f hcover h (by rw [hy', hφπ]) ?_
    rw [hy']
    exact hg
end IsBlowupAlongIdealSheaf
end FunctorialResolution.Blowup
