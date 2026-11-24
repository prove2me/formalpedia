-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.restrictIdeal_eq_of_stalkIdeal_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:15:41.58448+00:00
-- url     : https://prove2.me/submissions/ba68a8b7-0a6f-40cd-ab73-29b1f1645ee4

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartFiberProduct
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderPullback
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheafOrderDecrease
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheafSmoothPullback
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_TaylorExpansion
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_TaylorExpansionComparison
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_MaxContactIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_StalkIdealSpreadOut
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_ideal_eq_map_appLE
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
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
private theorem notMem_of_mem_primeCompl {R : Type*} [CommRing R] {m : Ideal R} [m.IsPrime]
    {x : R} (hx : x ∈ m.primeCompl) : x ∉ m := hx
private theorem exists_notMem_mul_mem_of_map_le {R : Type*} [CommRing R] (S : Type*) [CommRing S]
    [Algebra R S] (m : Ideal R) [hmp : m.IsPrime] [IsLocalization m.primeCompl S]
    {A B : Ideal R} (hAB : Ideal.map (algebraMap R S) A ≤ Ideal.map (algebraMap R S) B)
    {a : R} (ha : a ∈ A) : ∃ t : R, t ∉ m ∧ t * a ∈ B := by
  have hmem : algebraMap R S a ∈ Ideal.map (algebraMap R S) B :=
    hAB (Ideal.mem_map_of_mem _ ha)
  obtain ⟨⟨b, s⟩, hbs⟩ := (IsLocalization.mem_map_algebraMap_iff m.primeCompl S).mp hmem
  have hbs' : algebraMap R S (a * (s : R)) = algebraMap R S (b : R) := by
    rw [map_mul]
    exact hbs
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists m.primeCompl S).mp hbs'
  have hc2 : (c : R) ∉ m := notMem_of_mem_primeCompl c.2
  have hs2 : (s : R) ∉ m := notMem_of_mem_primeCompl s.2
  refine ⟨(c : R) * (s : R), ?_, ?_⟩
  · intro hcs
    rcases hmp.mem_or_mem hcs with h1 | h1
    · exact hc2 h1
    · exact hs2 h1
  · have hEq : ((c : R) * (s : R)) * a = (c : R) * (b : R) := by
      rw [← hc]
      ring
    rw [hEq]
    exact Ideal.mul_mem_left _ _ b.2
private theorem le_of_forall_isMaximal_exists_mul_mem {R : Type*} [CommRing R] {A B : Ideal R}
    (h : ∀ m : Ideal R, m.IsMaximal → ∀ a ∈ A, ∃ t : R, t ∉ m ∧ t * a ∈ B) : A ≤ B := by
  intro a ha
  by_contra hab
  obtain ⟨C, hCmem⟩ : ∃ C : Ideal R, ∀ r : R, r ∈ C ↔ r * a ∈ B := by
    refine ⟨{ carrier := {r : R | r * a ∈ B}
              add_mem' := ?_
              zero_mem' := ?_
              smul_mem' := ?_ }, fun r => Iff.rfl⟩
    · intro x y hx hy
      show (x + y) * a ∈ B
      rw [add_mul]
      exact B.add_mem hx hy
    · show (0 : R) * a ∈ B
      rw [zero_mul]
      exact B.zero_mem
    · intro c x hx
      show (c • x) * a ∈ B
      rw [smul_eq_mul, mul_assoc]
      exact Ideal.mul_mem_left _ _ hx
  have hCne : C ≠ ⊤ := by
    intro hCtop
    have h1 : (1 : R) ∈ C := by
      rw [hCtop]
      exact Submodule.mem_top
    have h2 := (hCmem 1).mp h1
    rw [one_mul] at h2
    exact hab h2
  obtain ⟨m, hm, hCm⟩ := Ideal.exists_le_maximal C hCne
  obtain ⟨t, htm, htB⟩ := h m hm a ha
  exact htm (hCm ((hCmem t).mpr htB))
private theorem ideal_le_of_stalkIdeal_le {Y : Scheme.{u}} (A B : Y.IdealSheafData)
    (W : Y.affineOpens) (h : ∀ x : ↥Y, x ∈ W.1 → stalkIdeal A x ≤ stalkIdeal B x) :
    A.ideal W ≤ B.ideal W := by
  refine le_of_forall_isMaximal_exists_mul_mem ?_
  intro m hm a ha
  have hmp : m.IsPrime := hm.isPrime
  set y : PrimeSpectrum Γ(Y, W.1) := ⟨m, hmp⟩ with hydef
  set x : ↥Y := W.2.fromSpec.base y with hxdef
  have hy : x ∈ W.1 := by
    have hmem : x ∈ Set.range (W.2.fromSpec.base) := ⟨y, rfl⟩
    rw [W.2.range_fromSpec] at hmem
    exact hmem
  let algI : Algebra Γ(Y, W.1) ↑(Y.presheaf.stalk x) :=
    (Y.presheaf.germ W.1 x hy).hom.toAlgebra
  have hloc : IsLocalization m.primeCompl ↑(Y.presheaf.stalk x) :=
    W.2.isLocalization_stalk' y hy
  refine exists_notMem_mul_mem_of_map_le (↑(Y.presheaf.stalk x)) m ?_ ha
  have halg : (algebraMap Γ(Y, W.1) ↑(Y.presheaf.stalk x))
      = (Y.presheaf.germ W.1 x hy).hom := rfl
  rw [halg, ← stalkIdeal_eq_map_germ A x W hy, ← stalkIdeal_eq_map_germ B x W hy]
  exact h x hy
private theorem ideal_eq_of_stalkIdeal_eq {Y : Scheme.{u}} (A B : Y.IdealSheafData)
    (W : Y.affineOpens) (h : ∀ x : ↥Y, x ∈ W.1 → stalkIdeal A x = stalkIdeal B x) :
    A.ideal W = B.ideal W :=
  le_antisymm (ideal_le_of_stalkIdeal_le A B W fun x hx => le_of_eq (h x hx))
    (ideal_le_of_stalkIdeal_le B A W fun x hx => le_of_eq (h x hx).symm)
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X : Scheme.{u}} (I J : X.IdealSheafData) (U : X.Opens)
    (h : ∀ y : X, y ∈ U → stalkIdeal I y = stalkIdeal J y) :
    restrictIdeal I U = restrictIdeal J U := by
  have key : ∀ V : U.toScheme.affineOpens,
      (restrictIdeal I U).ideal V = (restrictIdeal J U).ideal V := by
    intro V
    have hWaff : IsAffineOpen (U.ι ''ᵁ V.1) := V.2.image_of_isOpenImmersion U.ι
    have hWU : (U.ι ''ᵁ V.1) ≤ U := by
      intro z hz
      have hz' : z ∈ (fun w => U.ι.base w) '' (↑V.1 : Set U.toScheme) := hz
      obtain ⟨v, -, rfl⟩ := hz'
      exact v.2
    have e : V.1 ≤ U.ι ⁻¹ᵁ (U.ι ''ᵁ V.1) := by
      intro v hv
      have h2 : U.ι.base v ∈ (fun w => U.ι.base w) '' (↑V.1 : Set U.toScheme) := ⟨v, hv, rfl⟩
      exact h2
    have hIJ : I.ideal ⟨U.ι ''ᵁ V.1, hWaff⟩ = J.ideal ⟨U.ι ''ᵁ V.1, hWaff⟩ := by
      refine ideal_eq_of_stalkIdeal_eq I J ⟨U.ι ''ᵁ V.1, hWaff⟩ ?_
      intro z hz
      exact h z (hWU hz)
    show (I.comap U.ι).ideal V = (J.comap U.ι).ideal V
    rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE I U.ι ⟨U.ι ''ᵁ V.1, hWaff⟩ V e,
      Scheme.IdealSheafData.comap_ideal_eq_map_appLE J U.ι ⟨U.ι ''ᵁ V.1, hWaff⟩ V e, hIJ]
  have h1 : ∀ V : U.toScheme.affineOpens,
      (restrictIdeal I U).ideal V ≤ (restrictIdeal J U).ideal V := fun V => le_of_eq (key V)
  have h2 : ∀ V : U.toScheme.affineOpens,
      (restrictIdeal J U).ideal V ≤ (restrictIdeal I U).ideal V := fun V => le_of_eq (key V).symm
  exact le_antisymm h1 h2
end FunctorialResolution.EmbeddedResolution
