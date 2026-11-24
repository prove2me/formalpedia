-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.exists_etaleChart_genericPoint_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:45:17.693195+00:00
-- url     : https://prove2.me/submissions/629e26ff-f3dc-4525-a749-31048ecc930a

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisibility
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorSmoothness
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinatePolynomialRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderAtGenericPoint
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_notMem_support_of_mem_opens_of_restrictIdeal_eq_top
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isClosed_of_maximal_irreducible_subset_support
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_eq_span_germ_coord
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_isAffineOpen_mem
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mem_support_iff_stalkIdeal_ne_top
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_restrictIdeal_eq_restrict_coordIdeal_of_le

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
variable {X : Scheme.{u}} {k : Type u} [Field k] (p : X ⟶ Spec (CommRingCat.of k))
private theorem isUnit_germ_iff_notMem_primeIdealOf {Y : Scheme.{u}} {W : Y.Opens}
    (hW : IsAffineOpen W) (y : Y) (hy : y ∈ W) (f : Γ(Y, W)) :
    IsUnit ((Y.presheaf.germ W y hy).hom f) ↔ f ∉ (hW.primeIdealOf ⟨y, hy⟩).asIdeal := by
  let _ : Algebra (Γ(Y, W)) (Y.presheaf.stalk y) := (Y.presheaf.germ W y hy).hom.toAlgebra
  have : IsLocalization.AtPrime (Y.presheaf.stalk y) (hW.primeIdealOf ⟨y, hy⟩).asIdeal :=
    hW.isLocalization_stalk ⟨y, hy⟩
  constructor
  · intro hu hmem
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (↥(Y.presheaf.stalk y))
      (hW.primeIdealOf ⟨y, hy⟩).asIdeal f).mp hu hmem
  · intro hmem
    exact IsLocalization.map_units (S := Y.presheaf.stalk y)
      (M := (hW.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl) ⟨f, hmem⟩
private theorem primeIdealOf_le_of_specializes {Y : Scheme.{u}} {W : Y.Opens}
    (hW : IsAffineOpen W) (a b : Y) (ha : a ∈ W) (hb : b ∈ W) (h : a ⤳ b) :
    (hW.primeIdealOf ⟨a, ha⟩).asIdeal ≤ (hW.primeIdealOf ⟨b, hb⟩).asIdeal := by
  intro f hf
  by_contra hcon
  have hb' : b ∈ Y.basicOpen f :=
    (Scheme.mem_basicOpen Y f b hb).mpr ((isUnit_germ_iff_notMem_primeIdealOf hW b hb f).mpr hcon)
  have ha' : a ∈ Y.basicOpen f := h.mem_open (Y.basicOpen f).isOpen hb'
  exact ((isUnit_germ_iff_notMem_primeIdealOf hW a ha f).mp
    ((Scheme.mem_basicOpen Y f a ha).mp ha')) hf
private theorem specializes_of_primeIdealOf_le {Y : Scheme.{u}} {V : Y.Opens}
    (hV : IsAffineOpen V) (a b : Y) (ha : a ∈ V) (hb : b ∈ V)
    (h : (hV.primeIdealOf ⟨a, ha⟩).asIdeal ≤ (hV.primeIdealOf ⟨b, hb⟩).asIdeal) : a ⤳ b := by
  rw [specializes_iff_mem_closure, mem_closure_iff]
  intro W hWopen hbW
  have hbW' : b ∈ (⟨W, hWopen⟩ : Y.Opens) := hbW
  obtain ⟨f, hfW, hbf⟩ :=
    hV.exists_basicOpen_le (⟨b, hbW'⟩ : ↥(⟨W, hWopen⟩ : Y.Opens)) hb
  have hfb : f ∉ (hV.primeIdealOf ⟨b, hb⟩).asIdeal :=
    (isUnit_germ_iff_notMem_primeIdealOf hV b hb f).mp ((Scheme.mem_basicOpen Y f b hb).mp hbf)
  have hfa : f ∉ (hV.primeIdealOf ⟨a, ha⟩).asIdeal := fun hcon => hfb (h hcon)
  have haf : a ∈ Y.basicOpen f :=
    (Scheme.mem_basicOpen Y f a ha).mpr ((isUnit_germ_iff_notMem_primeIdealOf hV a ha f).mpr hfa)
  exact ⟨a, SetLike.le_def.mp hfW haf, rfl⟩
private theorem exists_mem_primeIdealOf_eq_of_isPrime {Y : Scheme.{u}} {V : Y.Opens} (hV : IsAffineOpen V)
    (P : Ideal Γ(Y, V)) (hP : P.IsPrime) :
    ∃ (ξ : Y) (hξ : ξ ∈ V), (hV.primeIdealOf ⟨ξ, hξ⟩).asIdeal = P := by
  have hsub : Set.range hV.fromSpec.base ⊆ (V : Set Y) := hV.range_fromSpec.subset
  have hmem : hV.fromSpec.base (⟨P, hP⟩ : PrimeSpectrum Γ(Y, V)) ∈ V :=
    hsub (Set.mem_range_self _)
  refine ⟨hV.fromSpec.base (⟨P, hP⟩ : PrimeSpectrum Γ(Y, V)), hmem, ?_⟩
  have h1 : hV.fromSpec.base (hV.primeIdealOf
      ⟨hV.fromSpec.base (⟨P, hP⟩ : PrimeSpectrum Γ(Y, V)), hmem⟩) =
      hV.fromSpec.base (⟨P, hP⟩ : PrimeSpectrum Γ(Y, V)) :=
    hV.fromSpec_primeIdealOf ⟨hV.fromSpec.base (⟨P, hP⟩ : PrimeSpectrum Γ(Y, V)), hmem⟩
  exact congrArg PrimeSpectrum.asIdeal (hV.fromSpec.isOpenEmbedding.injective h1)
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {X : Scheme.{u}} {k : Type u} [Field k] (p : X ⟶ Spec (CommRingCat.of k))
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (D : X.IdealSheafData)
    (hloc : ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U) (n : ℕ) (c : EtaleChart p U n),
      restrictIdeal D U = ⊤ ∨ ∃ j : Fin n, restrictIdeal D U = c.coordIdeal {j})
    {C : Set X} (hC : IsIrreducible C) (hCsub : C ⊆ (D.support : Set X))
    (hCmax : ∀ C' : Set X, IsIrreducible C' → C ⊆ C' → C' ⊆ (D.support : Set X) → C' = C)
    (x : X) (hx : x ∈ C) :
    ∃ (V : X.Opens) (hV : IsAffineOpen V) (_ : x ∈ V) (hη : hC.genericPoint ∈ V) (n : ℕ)
      (c : EtaleChart p V n) (j : Fin n),
      restrictIdeal D V = c.coordIdeal {j} ∧ hC.genericPoint ⤳ x ∧
        hC.genericPoint ∈ D.support ∧
        ∀ P : Ideal Γ(X, V), P.IsPrime → c.coord j ∈ P →
          P ≤ (hV.primeIdealOf ⟨hC.genericPoint, hη⟩).asIdeal →
          P = (hV.primeIdealOf ⟨hC.genericPoint, hη⟩).asIdeal := by
  have hCclosed : IsClosed C := isClosed_of_maximal_irreducible_subset_support D hC hCsub hCmax
  have hgen0 : closure ({hC.genericPoint} : Set X) = closure C :=
    (QuasiSober.sober hC.closure isClosed_closure).choose_spec
  have hgen : closure ({hC.genericPoint} : Set X) = C := by
    rw [hgen0]
    exact hCclosed.closure_eq
  have hηC : hC.genericPoint ∈ C := by
    have h1 : hC.genericPoint ∈ closure ({hC.genericPoint} : Set X) := subset_closure rfl
    rwa [hgen] at h1
  have hspec : hC.genericPoint ⤳ x := by
    have h1 : x ∈ closure ({hC.genericPoint} : Set X) := by
      rw [hgen]
      exact hx
    exact specializes_iff_mem_closure.mpr h1
  obtain ⟨U, hxU, n, c, hcase⟩ := hloc x
  have hxsupp : x ∈ D.support := hCsub hx
  have hne : ¬ (restrictIdeal D U = ⊤) := fun htop =>
    notMem_support_of_mem_opens_of_restrictIdeal_eq_top D U htop x hxU hxsupp
  obtain ⟨j, hDU⟩ := hcase.resolve_left hne
  obtain ⟨W, hxW, hW⟩ := Scheme.exists_isAffineOpen_mem x
  obtain ⟨f, hfU, hxf⟩ := hW.exists_basicOpen_le (⟨x, hxU⟩ : ↥U) hxW
  have hVaff : IsAffineOpen (X.basicOpen f) := hW.basicOpen f
  have hVU : X.basicOpen f ≤ U := hfU
  have hxV : x ∈ X.basicOpen f := hxf
  have hηV : hC.genericPoint ∈ X.basicOpen f := hspec.mem_open (X.basicOpen f).isOpen hxV
  have hDV : restrictIdeal D (X.basicOpen f) = (c.restrict hVU).coordIdeal {j} :=
    restrictIdeal_eq_restrict_coordIdeal_of_le hVU c D {j} hDU
  refine ⟨X.basicOpen f, hVaff, hxV, hηV, n, c.restrict hVU, j, hDV, hspec, hCsub hηC, ?_⟩
  intro P hP hcoord hPle
  obtain ⟨ξ, hξV, hξP⟩ := exists_mem_primeIdealOf_eq_of_isPrime hVaff P hP
  have hξsupp : ξ ∈ D.support := by
    rw [mem_support_iff_stalkIdeal_ne_top,
      stalkIdeal_eq_span_germ_coord p hVaff (c.restrict hVU) j D hDV ξ hξV]
    intro htop
    have hu := Ideal.span_singleton_eq_top.mp htop
    have hnot :=
      (isUnit_germ_iff_notMem_primeIdealOf hVaff ξ hξV ((c.restrict hVU).coord j)).mp hu
    rw [hξP] at hnot
    exact hnot hcoord
  have hξη : ξ ⤳ hC.genericPoint :=
    specializes_of_primeIdealOf_le hVaff ξ hC.genericPoint hξV hηV
      (by rw [hξP]; exact hPle)
  have hclosξ : closure ({ξ} : Set X) ⊆ (D.support : Set X) :=
    closure_minimal (Set.singleton_subset_iff.mpr hξsupp) D.support.2
  have hCsubξ : C ⊆ closure ({ξ} : Set X) := by
    have h1 : closure ({hC.genericPoint} : Set X) ⊆ closure ({ξ} : Set X) :=
      closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hξη))
        isClosed_closure
    rwa [hgen] at h1
  have hEq : closure ({ξ} : Set X) = C :=
    hCmax _ isIrreducible_singleton.closure hCsubξ hclosξ
  have hξC : ξ ∈ C := by
    have h1 : ξ ∈ closure ({ξ} : Set X) := subset_closure rfl
    rwa [hEq] at h1
  have hηξ : hC.genericPoint ⤳ ξ := by
    have h1 : ξ ∈ closure ({hC.genericPoint} : Set X) := by
      rw [hgen]
      exact hξC
    exact specializes_iff_mem_closure.mpr h1
  have hle2 : (hVaff.primeIdealOf ⟨hC.genericPoint, hηV⟩).asIdeal ≤ P := by
    rw [← hξP]
    exact primeIdealOf_le_of_specializes hVaff hC.genericPoint ξ hηV hξV hηξ
  exact le_antisymm hPle hle2
end FunctorialResolution.EmbeddedResolution
