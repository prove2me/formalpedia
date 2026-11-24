-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.le_pow_of_support_subset_orderAtLeastLocus_of_coordIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:23:19.069939+00:00
-- url     : https://prove2.me/submissions/d373086c-8fac-4f81-a4ed-4ea5fed7c948

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorSmoothness
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinatePolynomialRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealOrderDecrease
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheafOrderDecrease
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_PowerContainmentAndOrderLocus
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_ideal_le_pow_of_restrictIdeal_eq_coordIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mem_support_iff_stalkIdeal_le_maximalIdeal
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
open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace FunctorialResolution.EmbeddedResolution
private theorem mem_support_iff_ideal_le_primeIdealOf_of_isAffineOpen {X : Scheme.{u}} (I : X.IdealSheafData) {U : X.Opens}
    (hU : IsAffineOpen U) (x : U) :
    (x : X) ∈ I.support ↔ I.ideal ⟨U, hU⟩ ≤ (hU.primeIdealOf x).asIdeal := by
  have := hU.isLocalization_stalk x
  rw [mem_support_iff_stalkIdeal_le_maximalIdeal, stalkIdeal_eq_map_germ I (x : X) ⟨U, hU⟩ x.2]
  constructor
  · intro hle y hy
    have h2 : (X.presheaf.germ U (x : X) x.2).hom y ∈
        IsLocalRing.maximalIdeal ↑(X.presheaf.stalk (x : X)) := hle (Ideal.mem_map_of_mem _ hy)
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff
      (X.presheaf.stalk (x : X)) (hU.primeIdealOf x).asIdeal y).mp h2
  · intro hle
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff
      (X.presheaf.stalk (x : X)) (hU.primeIdealOf x).asIdeal y).mpr (hle hy)
private theorem exists_point_primeIdealOf_eq {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (q : PrimeSpectrum Γ(X, U)) : ∃ x : U, hU.primeIdealOf x = q := by
  have hmem : hU.fromSpec.base q ∈ U := by
    have h1 : hU.fromSpec.base q ∈ Set.range hU.fromSpec.base := ⟨q, rfl⟩
    rw [hU.range_fromSpec] at h1
    exact h1
  refine ⟨⟨hU.fromSpec.base q, hmem⟩, ?_⟩
  have hinj : Function.Injective hU.fromSpec.base := hU.fromSpec.isOpenEmbedding.injective
  apply hinj
  exact hU.fromSpec_primeIdealOf ⟨hU.fromSpec.base q, hmem⟩
private theorem notMem_primeIdealOf_of_mem_basicOpen {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (g : Γ(X, U)) (x : U) (hxg : (x : X) ∈ X.basicOpen g) :
    g ∉ (hU.primeIdealOf x).asIdeal := by
  have := hU.isLocalization_stalk x
  have hunit : IsUnit ((X.presheaf.germ U (x : X) x.2).hom g) :=
    (X.mem_basicOpen g (x : X) x.2).mp hxg
  intro hmem
  have h2 := (IsLocalization.AtPrime.to_map_mem_maximal_iff
    (X.presheaf.stalk (x : X)) (hU.primeIdealOf x).asIdeal g).mpr hmem
  exact (IsLocalRing.mem_maximalIdeal _).mp h2 hunit
private theorem ideal_eq_top_of_disjoint_support {X : Scheme.{u}} (Z : X.IdealSheafData)
    (W : X.affineOpens) (hW : ∀ y : X, y ∈ W.1 → y ∉ Z.support) : Z.ideal W = ⊤ := by
  by_contra hne
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
  have : P.IsPrime := hP.isPrime
  obtain ⟨x, hxq⟩ := exists_point_primeIdealOf_eq W.2 ⟨P, hP.isPrime⟩
  have hxq' : (W.2.primeIdealOf x).asIdeal = P := congrArg PrimeSpectrum.asIdeal hxq
  refine hW (x : X) x.2 ?_
  refine (mem_support_iff_ideal_le_primeIdealOf_of_isAffineOpen Z W.2 x).mpr ?_
  rw [hxq']
  exact hle
private theorem le_pow_of_forall_le_pow_basicOpen {X : Scheme.{u}} (Z I : X.IdealSheafData) (m : ℕ)
    (hloc : ∀ (V : X.affineOpens) (x : X), x ∈ V.1 →
      ∃ g : Γ(X, V.1), x ∈ X.basicOpen g ∧
        I.ideal (X.affineBasicOpen g) ≤ Z.ideal (X.affineBasicOpen g) ^ m) :
    I ≤ Z ^ m := by
  have key : ∀ V : X.affineOpens, I.ideal V ≤ (Z ^ m).ideal V := by
    intro V
    rw [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply]
    intro a ha
    by_contra hcon
    have hcol : ((Z.ideal V) ^ m).colon (Ideal.span {a}) ≠ ⊤ := by
      intro htop
      have h1 : (1 : Γ(X, V.1)) ∈ ((Z.ideal V) ^ m).colon (Ideal.span {a}) := by
        rw [htop]; exact Submodule.mem_top
      have h2 := Submodule.mem_colon.mp h1 a (Ideal.mem_span_singleton_self a)
      rw [smul_eq_mul, one_mul] at h2
      exact hcon h2
    obtain ⟨P, hP, hPle⟩ := Ideal.exists_le_maximal _ hcol
    have : P.IsPrime := hP.isPrime
    obtain ⟨x, hxq⟩ := exists_point_primeIdealOf_eq V.2 ⟨P, hP.isPrime⟩
    have hxq' : (V.2.primeIdealOf x).asIdeal = P := congrArg PrimeSpectrum.asIdeal hxq
    obtain ⟨g, hxg, hgle⟩ := hloc V (x : X) x.2
    have hgP : g ∉ P := by
      have hg := notMem_primeIdealOf_of_mem_basicOpen V.2 g x hxg
      rw [hxq'] at hg
      exact hg
    let _ : Algebra Γ(X, V.1) Γ(X, X.basicOpen g) :=
      (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom.toAlgebra
    have : IsLocalization.Away g Γ(X, X.basicOpen g) := V.2.isLocalization_basicOpen g
    have hI : Ideal.map (algebraMap Γ(X, V.1) Γ(X, X.basicOpen g)) (I.ideal V) =
        I.ideal (X.affineBasicOpen g) := I.map_ideal_basicOpen V g
    have hZ : Ideal.map (algebraMap Γ(X, V.1) Γ(X, X.basicOpen g)) (Z.ideal V) =
        Z.ideal (X.affineBasicOpen g) := Z.map_ideal_basicOpen V g
    have hmem : (algebraMap Γ(X, V.1) Γ(X, X.basicOpen g)) a ∈
        Ideal.map (algebraMap Γ(X, V.1) Γ(X, X.basicOpen g)) ((Z.ideal V) ^ m) := by
      rw [Ideal.map_pow, hZ]
      exact hgle (hI ▸ Ideal.mem_map_of_mem _ ha)
    rw [IsLocalization.mem_map_algebraMap_iff (Submonoid.powers g)] at hmem
    obtain ⟨⟨bb, sm⟩, heq⟩ := hmem
    rw [← map_mul] at heq
    obtain ⟨tm, hct⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers g)
      Γ(X, X.basicOpen g)).mp heq
    have hmemB : ((tm : Γ(X, V.1)) * (sm : Γ(X, V.1))) * a ∈ (Z.ideal V) ^ m := by
      have h3 : ((tm : Γ(X, V.1)) * (sm : Γ(X, V.1))) * a
          = (tm : Γ(X, V.1)) * (a * (sm : Γ(X, V.1))) := by ring
      rw [h3, hct]
      exact Ideal.mul_mem_left _ _ bb.2
    have hcolmem : ((tm : Γ(X, V.1)) * (sm : Γ(X, V.1))) ∈
        ((Z.ideal V) ^ m).colon (Ideal.span {a}) := by
      refine Submodule.mem_colon.mpr ?_
      intro q hq
      obtain ⟨cc, rfl⟩ := Ideal.mem_span_singleton'.mp hq
      have h4 : ((tm : Γ(X, V.1)) * (sm : Γ(X, V.1))) • (cc * a)
          = cc * (((tm : Γ(X, V.1)) * (sm : Γ(X, V.1))) * a) := by
        rw [smul_eq_mul]; ring
      rw [h4]
      exact Ideal.mul_mem_left _ _ hmemB
    obtain ⟨i, hi⟩ := tm.2
    obtain ⟨j, hj⟩ := sm.2
    have hts : (tm : Γ(X, V.1)) * (sm : Γ(X, V.1)) = g ^ (i + j) := by
      rw [← hi, ← hj, pow_add]
    have hmemP : g ^ (i + j) ∈ P := hts ▸ hPle hcolmem
    exact hgP (hP.isPrime.mem_of_pow_mem _ hmemP)
  exact key
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
universe u
open AlgebraicGeometry CategoryTheory TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X : Scheme.{u}} {k : Type u} [Field k] [CharZero k]
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] (Z I : X.IdealSheafData)
    (m : ℕ)
    (hchart : ∀ x : X, x ∈ Z.support →
      ∃ (U : X.Opens) (_ : x ∈ U) (n : ℕ) (c : EtaleChart p U n) (S : Finset (Fin n)),
        restrictIdeal Z U = c.coordIdeal S)
    (hord : (Z.support : Set X) ⊆ orderAtLeastLocus I m) :
    I ≤ Z ^ m := by
  refine le_pow_of_forall_le_pow_basicOpen Z I m ?_
  intro V x hx
  by_cases hxZ : x ∈ Z.support
  · obtain ⟨U, hxU, n, c, S, hS⟩ := hchart x hxZ
    obtain ⟨g, hgU, hxg⟩ := V.2.exists_basicOpen_le (⟨x, hxU⟩ : U) hx
    refine ⟨g, hxg, ?_⟩
    have hWaff : IsAffineOpen (X.basicOpen g) := V.2.basicOpen g
    have hchart' : restrictIdeal Z (X.basicOpen g) = (c.restrict hgU).coordIdeal S :=
      restrictIdeal_eq_restrict_coordIdeal_of_le hgU c Z S hS
    exact ideal_le_pow_of_restrictIdeal_eq_coordIdeal p hWaff (c.restrict hgU) Z S hchart' m I
      (fun y hy _ => hord hy)
  · have hΩopen : IsOpen ((Z.support : Set X)ᶜ) := Z.support.2.isOpen_compl
    have hxΩ : x ∈ (⟨(Z.support : Set X)ᶜ, hΩopen⟩ : X.Opens) := hxZ
    obtain ⟨g, hgΩ, hxg⟩ :=
      V.2.exists_basicOpen_le (⟨x, hxΩ⟩ : (⟨(Z.support : Set X)ᶜ, hΩopen⟩ : X.Opens)) hx
    refine ⟨g, hxg, ?_⟩
    have htop : Z.ideal (X.affineBasicOpen g) = ⊤ := by
      refine ideal_eq_top_of_disjoint_support Z (X.affineBasicOpen g) ?_
      intro y hy
      have hy' : y ∈ X.basicOpen g := hy
      exact hgΩ hy'
    rw [htop, ← Ideal.one_eq_top, one_pow, Ideal.one_eq_top]
    exact le_top
end FunctorialResolution.EmbeddedResolution
