-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.IsIrreducibleComponentOfSupport.exists_affineOpen_etaleChart_coordIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:21:50.2334+00:00
-- url     : https://prove2.me/submissions/647e0445-0ca5-4213-89cc-72db36bbc995

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorSmoothness
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_PowerContainmentAndOrderLocus
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderAtGenericPoint
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IrreducibleComponentsOfSupport
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_exists_isIrreducibleComponentOfSupport
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_finite_isIrreducibleComponentOfSupport
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_IsIrreducibleComponentOfSupport_disjoint
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_mem_support_iff_ideal_le_primeIdealOf
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_affineOpens_mem_le
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isRadical_ideal_of_restrictIdeal_eq_coordIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mem_support_iff_stalkIdeal_le_maximalIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_notMem_support_of_mem_opens_of_restrictIdeal_eq_top
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_restrictIdeal_eq_restrict_coordIdeal_of_le
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_eq_map_germ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
private theorem exists_fromSpec_mem_and_primeIdealOf_eq {X : Scheme.{u}} {V : X.Opens} (hV : IsAffineOpen V)
    (P : PrimeSpectrum Γ(X, V)) :
    ∃ hz : hV.fromSpec.base P ∈ V, hV.primeIdealOf ⟨hV.fromSpec.base P, hz⟩ = P := by
  have hz : hV.fromSpec.base P ∈ V := by
    have h : hV.fromSpec.base P ∈ Set.range hV.fromSpec.base := ⟨P, rfl⟩
    rwa [hV.range_fromSpec] at h
  refine ⟨hz, hV.fromSpec.isOpenEmbedding.injective ?_⟩
  rw [hV.fromSpec_primeIdealOf]
private theorem mem_support_iff_ideal_le_primeIdealOf {X : Scheme.{u}} (I : X.IdealSheafData)
    {V : X.Opens} (hV : IsAffineOpen V) {x : ↥X} (hx : x ∈ V) :
    x ∈ I.support ↔ I.ideal ⟨V, hV⟩ ≤ (hV.primeIdealOf ⟨x, hx⟩).asIdeal := by
  let _ : Algebra ↑Γ(X, V) ↑(X.presheaf.stalk x) :=
    RingHom.toAlgebra (X.presheaf.germ V x hx).hom
  have : IsLocalization.AtPrime ↑(X.presheaf.stalk x) (hV.primeIdealOf ⟨x, hx⟩).asIdeal :=
    hV.isLocalization_stalk ⟨x, hx⟩
  have hcomap : Ideal.comap (X.presheaf.germ V x hx).hom
      (IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x))
      = (hV.primeIdealOf ⟨x, hx⟩).asIdeal := by
    have h := IsLocalization.AtPrime.under_maximalIdeal (R := ↑Γ(X, V))
      (S := ↑(X.presheaf.stalk x)) (I := (hV.primeIdealOf ⟨x, hx⟩).asIdeal)
    exact h
  rw [mem_support_iff_stalkIdeal_le_maximalIdeal, stalkIdeal_eq_map_germ I x ⟨V, hV⟩ hx,
    Ideal.map_le_iff_le_comap]
  exact iff_of_eq (congrArg (fun J => I.ideal ⟨V, hV⟩ ≤ J) hcomap)
private theorem vanishingIdeal_ideal_le_primeIdealOf {X : Scheme.{u}} (Z : Closeds ↥X)
    {V : X.Opens} (hV : IsAffineOpen V) {x : ↥X} (hx : x ∈ V) (hxZ : x ∈ (Z : Set ↥X)) :
    (Scheme.IdealSheafData.vanishingIdeal Z).ideal ⟨V, hV⟩
      ≤ (hV.primeIdealOf ⟨x, hx⟩).asIdeal := by
  have heq : (Scheme.IdealSheafData.vanishingIdeal Z).ideal ⟨V, hV⟩
      = PrimeSpectrum.vanishingIdeal (hV.fromSpec.base ⁻¹' (Z : Set ↥X)) := rfl
  intro f hf
  rw [heq, PrimeSpectrum.mem_vanishingIdeal] at hf
  refine hf (hV.primeIdealOf ⟨x, hx⟩) ?_
  have : hV.fromSpec.base (hV.primeIdealOf ⟨x, hx⟩) = x := hV.fromSpec_primeIdealOf ⟨x, hx⟩
  show hV.fromSpec.base (hV.primeIdealOf ⟨x, hx⟩) ∈ (Z : Set ↥X)
  rw [this]
  exact hxZ
private theorem le_vanishingIdeal_of_subset_support {X : Scheme.{u}} (I : X.IdealSheafData)
    (Z : Closeds ↥X) (h : (Z : Set ↥X) ⊆ (I.support : Set ↥X)) :
    I ≤ Scheme.IdealSheafData.vanishingIdeal Z := by
  have key : ∀ U : X.affineOpens,
      I.ideal U ≤ (Scheme.IdealSheafData.vanishingIdeal Z).ideal U := by
    intro U f hf
    have heq : (Scheme.IdealSheafData.vanishingIdeal Z).ideal U
        = PrimeSpectrum.vanishingIdeal (U.2.fromSpec.base ⁻¹' (Z : Set ↥X)) := rfl
    rw [heq, PrimeSpectrum.mem_vanishingIdeal]
    intro P hP
    obtain ⟨hz, hzP⟩ := exists_fromSpec_mem_and_primeIdealOf_eq U.2 P
    have hzs : U.2.fromSpec.base P ∈ I.support := h hP
    rw [mem_support_iff_ideal_le_primeIdealOf I U.2 hz, hzP] at hzs
    exact hzs hf
  exact key
namespace IsIrreducibleComponentOfSupport
variable {X : Scheme.{u}} {D : X.IdealSheafData} {C : Set X}
end IsIrreducibleComponentOfSupport
private theorem vanishingIdeal_ideal_eq_of_restrictIdeal_eq_coordIdeal {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} (D : X.IdealSheafData) {C : Set ↥X} (hCcl : IsClosed C)
    (hCsub : C ⊆ (D.support : Set ↥X))
    {W : X.Opens} (hW : IsAffineOpen W) {n : ℕ} (c : EtaleChart p W n) (S : Finset (Fin n))
    (hD : restrictIdeal D W = c.coordIdeal S)
    (hWC : ∀ y : ↥X, y ∈ W → y ∈ (D.support : Set ↥X) → y ∈ C) :
    (Scheme.IdealSheafData.vanishingIdeal (⟨C, hCcl⟩ : Closeds ↥X)).ideal ⟨W, hW⟩
      = D.ideal ⟨W, hW⟩ := by
  refine le_antisymm ?_ ?_
  · have hrad : (D.ideal ⟨W, hW⟩).IsRadical :=
      isRadical_ideal_of_restrictIdeal_eq_coordIdeal p hW c D S hD
    have hJ : D.ideal ⟨W, hW⟩ = sInf {P : Ideal Γ(X, W) | D.ideal ⟨W, hW⟩ ≤ P ∧ P.IsPrime} := by
      rw [← Ideal.radical_eq_sInf, hrad.radical]
    rw [hJ]
    refine le_sInf ?_
    rintro P ⟨hPle, hPprime⟩
    obtain ⟨hz, hzP⟩ := exists_fromSpec_mem_and_primeIdealOf_eq hW ⟨P, hPprime⟩
    have hzs : hW.fromSpec.base (⟨P, hPprime⟩ : PrimeSpectrum Γ(X, W)) ∈ D.support := by
      rw [mem_support_iff_ideal_le_primeIdealOf D hW hz, hzP]
      exact hPle
    have hzC : hW.fromSpec.base (⟨P, hPprime⟩ : PrimeSpectrum Γ(X, W)) ∈ C := hWC _ hz hzs
    have hfinal : (Scheme.IdealSheafData.vanishingIdeal (⟨C, hCcl⟩ : Closeds ↥X)).ideal ⟨W, hW⟩
        ≤ (hW.primeIdealOf ⟨_, hz⟩).asIdeal :=
      vanishingIdeal_ideal_le_primeIdealOf (⟨C, hCcl⟩ : Closeds ↥X) hW hz hzC
    rw [hzP] at hfinal
    exact hfinal
  · exact le_vanishingIdeal_of_subset_support D (⟨C, hCcl⟩ : Closeds ↥X) hCsub ⟨W, hW⟩
namespace IsIrreducibleComponentOfSupport
variable {X : Scheme.{u}} {D : X.IdealSheafData} {C : Set X}
variable {k : Type u} [Field k]
end IsIrreducibleComponentOfSupport
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.IsIrreducibleComponentOfSupport
variable {X : Scheme.{u}} {D : X.IdealSheafData} {C : Set X}
variable {k : Type u} [Field k]
namespace FunctorialResolution.EmbeddedResolution.IsIrreducibleComponentOfSupport
theorem _root_.solution [TopologicalSpace.NoetherianSpace ↥X] (hC : IsIrreducibleComponentOfSupport D C)
    (p : X ⟶ Spec (CommRingCat.of k))
    (hloc : ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U) (n : ℕ) (c : EtaleChart p U n),
      restrictIdeal D U = ⊤ ∨ ∃ j : Fin n, restrictIdeal D U = c.coordIdeal {j})
    (x : X) (hx : x ∈ C) :
    ∃ (V : X.Opens) (hV : IsAffineOpen V) (_ : x ∈ V) (n : ℕ) (c : EtaleChart p V n) (j : Fin n),
      restrictIdeal D V = c.coordIdeal {j} ∧
      (∀ y : X, y ∈ V → y ∈ (D.support : Set X) → y ∈ C) ∧
      (Scheme.IdealSheafData.vanishingIdeal
          (⟨C, hC.isClosed⟩ : TopologicalSpace.Closeds ↥X)).ideal ⟨V, hV⟩ = D.ideal ⟨V, hV⟩ ∧
      (∀ W : X.affineOpens, (↑W : X.Opens) ≤ V →
        (Scheme.IdealSheafData.vanishingIdeal
          (⟨C, hC.isClosed⟩ : TopologicalSpace.Closeds ↥X)).ideal W = D.ideal W) ∧
      (∀ y : X, y ∈ V →
        stalkIdeal (Scheme.IdealSheafData.vanishingIdeal
          (⟨C, hC.isClosed⟩ : TopologicalSpace.Closeds ↥X)) y = stalkIdeal D y) := by
  obtain ⟨U, hxU, n, c₀, hU⟩ := hloc x
  have hxs : x ∈ (D.support : Set X) := hC.subset_support hx
  have hDUex : ∃ j : Fin n, restrictIdeal D U = c₀.coordIdeal {j} := by
    rcases hU with h | h
    · exact absurd hxs (notMem_support_of_mem_opens_of_restrictIdeal_eq_top D U h x hxU)
    · exact h
  obtain ⟨j, hDU⟩ := hDUex
  obtain ⟨B, hBclosed, hxB, hBmem⟩ :
      ∃ B : Set ↥X, IsClosed B ∧ x ∉ B ∧
        ∀ y : ↥X, y ∈ (D.support : Set X) → y ∉ B → y ∈ C := by
    refine ⟨⋃ C'' ∈ {C'' : Set X | IsIrreducibleComponentOfSupport D C''} \ {C}, C'', ?_, ?_, ?_⟩
    · refine Set.Finite.isClosed_biUnion
        ((finite_isIrreducibleComponentOfSupport D).subset Set.sdiff_subset) ?_
      intro C'' hC''
      exact hC''.1.isClosed
    · intro hmem
      obtain ⟨C'', hC''mem, hxC''⟩ := Set.mem_iUnion₂.mp hmem
      exact Set.disjoint_left.mp
        (hC.disjoint hC''mem.1 p hloc (fun h => hC''mem.2 h.symm)) hx hxC''
    · intro y hys hyB
      obtain ⟨C'', hC''comp, hyC''⟩ := exists_isIrreducibleComponentOfSupport D y hys
      by_cases h : C'' = C
      · exact h ▸ hyC''
      · exact absurd (Set.mem_iUnion₂.mpr ⟨C'', ⟨hC''comp, h⟩, hyC''⟩) hyB
  have hxUB : x ∈ (⟨(U : Set ↥X) ∩ Bᶜ, U.isOpen.inter hBclosed.isOpen_compl⟩ : X.Opens) :=
    ⟨hxU, hxB⟩
  obtain ⟨V, hxV, hVle⟩ := Scheme.exists_affineOpens_mem_le hxUB
  have hVU : (V : X.Opens) ≤ U := fun y hy => (hVle hy).1
  have hVB : ∀ y : ↥X, y ∈ (V : X.Opens) → y ∉ B := fun y hy => (hVle hy).2
  have hDV : restrictIdeal D (V : X.Opens) = (c₀.restrict hVU).coordIdeal {j} :=
    restrictIdeal_eq_restrict_coordIdeal_of_le hVU c₀ D {j} hDU
  have hVC : ∀ y : X, y ∈ (V : X.Opens) → y ∈ (D.support : Set X) → y ∈ C :=
    fun y hy hys => hBmem y hys (hVB y hy)
  have key : ∀ W : X.affineOpens, (W : X.Opens) ≤ (V : X.Opens) →
      (Scheme.IdealSheafData.vanishingIdeal
        (⟨C, hC.isClosed⟩ : Closeds ↥X)).ideal W = D.ideal W := by
    intro W hWV
    have hDW : restrictIdeal D (W : X.Opens)
        = ((c₀.restrict hVU).restrict hWV).coordIdeal {j} :=
      restrictIdeal_eq_restrict_coordIdeal_of_le hWV (c₀.restrict hVU) D {j} hDV
    exact vanishingIdeal_ideal_eq_of_restrictIdeal_eq_coordIdeal D hC.isClosed hC.subset_support W.2
      ((c₀.restrict hVU).restrict hWV) {j} hDW
      (fun y hy hys => hVC y (hWV hy) hys)
  refine ⟨(V : X.Opens), V.2, hxV, n, c₀.restrict hVU, j, hDV, hVC, key V le_rfl, ?_, ?_⟩
  · intro W hWV
    exact key W hWV
  · intro y hy
    rw [stalkIdeal_eq_map_germ
        (Scheme.IdealSheafData.vanishingIdeal (⟨C, hC.isClosed⟩ : Closeds ↥X)) y V hy,
      stalkIdeal_eq_map_germ D y V hy, key V le_rfl]
end FunctorialResolution.EmbeddedResolution.IsIrreducibleComponentOfSupport
