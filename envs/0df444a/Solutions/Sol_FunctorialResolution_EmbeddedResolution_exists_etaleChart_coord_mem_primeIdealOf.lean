-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.exists_etaleChart_coord_mem_primeIdealOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:40:38.404169+00:00
-- url     : https://prove2.me/submissions/3a2f089a-47bd-4858-a376-7c735e0c4b65

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorSmoothness
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossingsChartNormalization
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_ideal_eq_span_image
import Theorems.Thm_Derivation_liftToLocalization_algebraMap
import Theorems.Thm_Derivation_mapToLocalization_algebraMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coordRingHom_X
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ideal_eq_span_coord
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ofCoords_map
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_basisDerivation_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheaf_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_pullbackCoord_def
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_restrictIdeal_eq_restrict_coordIdeal_of_le
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_restrictIdeal_eq_top_of_le
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_restrictIdeal_eq_comap___a4ce28546e44
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Derivation.liftToLocalization_algebraMap
attribute [local simp] Derivation.mapToLocalization_algebraMap
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleChart.coordRingHom_X
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleChart.ofCoords_map
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.basisDerivation_apply
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInl_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInl_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInr_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInr_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheaf_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.pullbackCoord_def


section
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
private theorem eq_some_and_not_of_bind_ite_eq_some {n : ℕ} (P : Fin n → Prop) [DecidablePred P]
    {o : Option (Fin n)} {j : Fin n}
    (h : o.bind (fun j0 => if P j0 then none else some j0) = some j) : o = some j ∧ ¬ P j := by
  cases o with
  | none => simp at h
  | some j0 =>
    by_cases hb : P j0
    · simp [hb] at h
    · simp [hb] at h
      subst h
      exact ⟨rfl, hb⟩
private theorem of_bind_ite_eq_none {n : ℕ} (P : Fin n → Prop) [DecidablePred P]
    {o : Option (Fin n)} {j : Fin n} (hg : o = some j)
    (h : o.bind (fun j0 => if P j0 then none else some j0) = none) : P j := by
  subst hg
  by_contra hb
  simp [hb] at h
private theorem eq_top_of_forall_ideal_eq_top {X : Scheme.{u}} (I : X.IdealSheafData)
    (h : ∀ W : X.affineOpens, I.ideal W = ⊤) : I = ⊤ := by
  have hfun : I.ideal = (⊤ : X.IdealSheafData).ideal := by
    funext W
    have htop : (⊤ : X.IdealSheafData).ideal W = ⊤ := rfl
    rw [h W, htop]
  exact Scheme.IdealSheafData.ext hfun
private theorem mem_support_iff_forall_notMem_basicOpen {X : Scheme.{u}} (I : X.IdealSheafData)
    {x : ↥X} {U : X.Opens} (hU : IsAffineOpen U) (hx : x ∈ U) :
    x ∈ I.support ↔ ∀ f ∈ I.ideal ⟨U, hU⟩, x ∉ X.basicOpen f := by
  have h0 : x ∈ I.support ↔
      x ∈ X.zeroLocus (↑(I.ideal ⟨U, hU⟩) : Set Γ(X, U)) :=
    Scheme.IdealSheafData.mem_support_iff_of_mem hx
  rw [h0, Scheme.mem_zeroLocus_iff]
  exact Iff.rfl
private theorem mem_basicOpen_iff_notMem_primeIdealOf {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (f : Γ(X, U)) (x : ↥U) :
    (x : ↥X) ∈ X.basicOpen f ↔ f ∉ (hU.primeIdealOf x).asIdeal := by
  have h2 : (AlgebraicGeometry.IsAffineOpen.fromSpec hU).base
      (AlgebraicGeometry.IsAffineOpen.primeIdealOf hU x) = (x : ↥X) :=
    AlgebraicGeometry.IsAffineOpen.fromSpec_primeIdealOf hU x
  have h1 : AlgebraicGeometry.IsAffineOpen.fromSpec hU ⁻¹ᵁ X.basicOpen f
      = PrimeSpectrum.basicOpen f :=
    AlgebraicGeometry.IsAffineOpen.fromSpec_preimage_basicOpen hU f
  constructor
  · intro hx
    have hmem : AlgebraicGeometry.IsAffineOpen.primeIdealOf hU x
        ∈ AlgebraicGeometry.IsAffineOpen.fromSpec hU ⁻¹ᵁ X.basicOpen f := by
      show (AlgebraicGeometry.IsAffineOpen.fromSpec hU).base
        (AlgebraicGeometry.IsAffineOpen.primeIdealOf hU x) ∈ X.basicOpen f
      rw [h2]
      exact hx
    rw [h1] at hmem
    exact (PrimeSpectrum.mem_basicOpen f _).mp hmem
  · intro hx
    have hmem : AlgebraicGeometry.IsAffineOpen.primeIdealOf hU x ∈ PrimeSpectrum.basicOpen f :=
      (PrimeSpectrum.mem_basicOpen f _).mpr hx
    rw [← h1] at hmem
    have h3 : (AlgebraicGeometry.IsAffineOpen.fromSpec hU).base
        (AlgebraicGeometry.IsAffineOpen.primeIdealOf hU x) ∈ X.basicOpen f := hmem
    rw [h2] at h3
    exact h3
private theorem mem_support_of_ideal_eq_span_singleton {X : Scheme.{u}} (I : X.IdealSheafData) {x : ↥X}
    {U : X.Opens} (hU : IsAffineOpen U) (hx : x ∈ U) (g : Γ(X, U))
    (hI : I.ideal ⟨U, hU⟩ = Ideal.span {g}) (hg : x ∉ X.basicOpen g) : x ∈ I.support := by
  rw [mem_support_iff_forall_notMem_basicOpen I hU hx]
  intro f hf
  rw [hI, Ideal.mem_span_singleton] at hf
  obtain ⟨a, rfl⟩ := hf
  have hle : X.basicOpen (g * a) ≤ X.basicOpen g := by
    rw [Scheme.basicOpen_mul]
    exact inf_le_left
  exact fun hc => hg (hle hc)
private theorem mem_primeIdealOf_of_mem_support_of_ideal_eq_span_singleton {X : Scheme.{u}} (I : X.IdealSheafData) {x : ↥X}
    {U : X.Opens} (hU : IsAffineOpen U) (hx : x ∈ U) (g : Γ(X, U))
    (hI : I.ideal ⟨U, hU⟩ = Ideal.span {g}) (hs : x ∈ I.support) :
    g ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
  have h := (mem_support_iff_forall_notMem_basicOpen I hU hx).mp hs g
    (by rw [hI]; exact Ideal.mem_span_singleton_self g)
  by_contra hc
  exact h ((mem_basicOpen_iff_notMem_primeIdealOf hU g ⟨x, hx⟩).mpr hc)
private theorem restrictIdeal_eq_top_of_le_basicOpen {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (I : X.IdealSheafData) (f : Γ(X, U))
    (hI : I.ideal ⟨U, hU⟩ = Ideal.span {f}) {V : X.Opens} (hVb : V ≤ X.basicOpen f) :
    restrictIdeal I V = ⊤ := by
  have hbU : X.basicOpen f ≤ U := X.basicOpen_le f
  have hVU : V ≤ U := hVb.trans hbU
  rw [restrictIdeal_eq_comap_ι]
  refine eq_top_of_forall_ideal_eq_top _ ?_
  intro Wa
  have e : (Wa : (V.toScheme).Opens) ≤ V.ι ⁻¹ᵁ U := fun x _ => hVU x.2
  have e' : (Wa : (V.toScheme).Opens) ≤ V.ι ⁻¹ᵁ X.basicOpen f := fun x _ => hVb x.2
  rw [Scheme.IdealSheafData.comap_ideal_eq_span_image I V.ι ⟨U, hU⟩ Wa e {f} hI,
    Set.image_singleton, Ideal.span_singleton_eq_top]
  have hfac : V.ι.appLE U (Wa : (V.toScheme).Opens) e
      = X.presheaf.map (homOfLE hbU).op ≫
        V.ι.appLE (X.basicOpen f) (Wa : (V.toScheme).Opens) e' := by
    rw [Scheme.Hom.map_appLE]
  have hcp : ((X.presheaf.map (homOfLE hbU).op ≫
        V.ι.appLE (X.basicOpen f) (Wa : (V.toScheme).Opens) e').hom) f
      = (V.ι.appLE (X.basicOpen f) (Wa : (V.toScheme).Opens) e').hom
          ((X.presheaf.map (homOfLE hbU).op).hom f) := rfl
  rw [hfac, hcp]
  exact IsUnit.map _ (X.toRingedSpace.isUnit_res_basicOpen f)
section
variable {Y Y' : Scheme.{u}} {k : Type u} [Field k] {p : Y ⟶ Spec (CommRingCat.of k)}
  {V : Y.Opens} {n : ℕ}
end
section
variable {X : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)}
end
section
variable {W : Scheme.{u}} {k : Type u} [Field k]
end
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {X : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)}
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (F : List X.IdealSheafData) (y : ↥X) (U : X.Opens)
    (hU : IsAffineOpen U) (hyU : y ∈ U) {n : ℕ} (c : EtaleChart p U n) (γ : ℕ → Option (Fin n))
    (hdesc : ∀ i, ∀ hi : i < F.length,
      (γ i = none → restrictIdeal (F[i]'hi) U = ⊤) ∧
        ∀ j, γ i = some j → restrictIdeal (F[i]'hi) U = c.coordIdeal {j})
    (hinj : ∀ i i', i < F.length → i' < F.length → ∀ j, γ i = some j → γ i' = some j → i = i') :
    ∃ (U' : X.Opens) (hU' : IsAffineOpen U') (hy' : y ∈ U') (n' : ℕ)
      (c' : EtaleChart p U' n') (γ' : ℕ → Option (Fin n')),
      (∀ i, ∀ hi : i < F.length,
        (γ' i = none → restrictIdeal (F[i]'hi) U' = ⊤) ∧
          ∀ j, γ' i = some j → restrictIdeal (F[i]'hi) U' = c'.coordIdeal {j}) ∧
      (∀ i i', i < F.length → i' < F.length → ∀ j, γ' i = some j → γ' i' = some j → i = i') ∧
      (∀ i, i < F.length → ∀ j, γ' i = some j →
        c'.coord j ∈ (hU'.primeIdealOf ⟨y, hy'⟩).asIdeal) := by
  classical
  set notInPrime : Finset (Fin n) :=
    Finset.univ.filter (fun j => c.coord j ∉ (hU.primeIdealOf ⟨y, hyU⟩).asIdeal) with hBadDef
  have hBad : ∀ j : Fin n, j ∈ notInPrime ↔ c.coord j ∉ (hU.primeIdealOf ⟨y, hyU⟩).asIdeal := by
    intro j
    rw [hBadDef]
    simp
  set t : Γ(X, U) := ∏ j ∈ notInPrime, c.coord j with htdef
  have ht : t ∉ (hU.primeIdealOf ⟨y, hyU⟩).asIdeal := by
    have hmem : ∀ j ∈ notInPrime, c.coord j ∈ Ideal.primeCompl (hU.primeIdealOf ⟨y, hyU⟩).asIdeal :=
      fun j hj => (hBad j).mp hj
    have hprod := Submonoid.prod_mem (Ideal.primeCompl (hU.primeIdealOf ⟨y, hyU⟩).asIdeal) hmem
    rw [← htdef] at hprod
    exact hprod
  have hUt : IsAffineOpen (X.basicOpen t) := hU.basicOpen t
  have hle : X.basicOpen t ≤ U := X.basicOpen_le t
  have hy' : y ∈ X.basicOpen t := (mem_basicOpen_iff_notMem_primeIdealOf hU t ⟨y, hyU⟩).mpr ht
  have hbasic_le : ∀ j ∈ notInPrime, X.basicOpen t ≤ X.basicOpen (c.coord j) := by
    intro j hj
    have hsplit : t = c.coord j * ∏ i ∈ notInPrime.erase j, c.coord i := by
      rw [htdef]
      exact (Finset.mul_prod_erase notInPrime (fun i => c.coord i) hj).symm
    rw [hsplit, Scheme.basicOpen_mul]
    exact inf_le_left
  refine ⟨X.basicOpen t, hUt, hy', n, c.restrict hle,
    fun i => (γ i).bind (fun j0 => if j0 ∈ notInPrime then none else some j0), ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨hA, hB⟩ := hdesc i hi
    constructor
    · intro hnone
      have hnone' : (γ i).bind (fun j0 => if j0 ∈ notInPrime then none else some j0) = none := hnone
      by_cases hg : γ i = none
      · exact restrictIdeal_eq_top_of_le _ hle (hA hg)
      · obtain ⟨j0, hj0⟩ := Option.ne_none_iff_exists'.mp hg
        have hb : j0 ∈ notInPrime := of_bind_ite_eq_none (fun j1 => j1 ∈ notInPrime) hj0 hnone'
        have hideal : (F[i]'hi).ideal ⟨U, hU⟩ = Ideal.span {c.coord j0} := by
          rw [c.ideal_eq_span_coord hU _ _ (hB j0 hj0), Finset.coe_singleton,
            Set.image_singleton]
        exact restrictIdeal_eq_top_of_le_basicOpen hU _ (c.coord j0) hideal (hbasic_le j0 hb)
    · intro j hj
      have hj' : (γ i).bind (fun j0 => if j0 ∈ notInPrime then none else some j0) = some j := hj
      obtain ⟨hg, hb⟩ := eq_some_and_not_of_bind_ite_eq_some (fun j1 => j1 ∈ notInPrime) hj'
      exact restrictIdeal_eq_restrict_coordIdeal_of_le hle c _ _ (hB j hg)
  · intro i i' hi hi' j hj hj'
    have hja : (γ i).bind (fun j0 => if j0 ∈ notInPrime then none else some j0) = some j := hj
    have hjb : (γ i').bind (fun j0 => if j0 ∈ notInPrime then none else some j0) = some j := hj'
    exact hinj i i' hi hi' j (eq_some_and_not_of_bind_ite_eq_some (fun j1 => j1 ∈ notInPrime) hja).1
      (eq_some_and_not_of_bind_ite_eq_some (fun j1 => j1 ∈ notInPrime) hjb).1
  · intro i hi j hj
    obtain ⟨_, hB⟩ := hdesc i hi
    have hj' : (γ i).bind (fun j0 => if j0 ∈ notInPrime then none else some j0) = some j := hj
    obtain ⟨hg, hb⟩ := eq_some_and_not_of_bind_ite_eq_some (fun j1 => j1 ∈ notInPrime) hj'
    have hmemP : c.coord j ∈ (hU.primeIdealOf ⟨y, hyU⟩).asIdeal := by
      by_contra hcon
      exact hb ((hBad j).mpr hcon)
    have hidU : (F[i]'hi).ideal ⟨U, hU⟩ = Ideal.span {c.coord j} := by
      rw [c.ideal_eq_span_coord hU _ _ (hB j hg), Finset.coe_singleton, Set.image_singleton]
    have hynb : y ∉ X.basicOpen (c.coord j) := fun hc =>
      (mem_basicOpen_iff_notMem_primeIdealOf hU (c.coord j) ⟨y, hyU⟩).mp hc hmemP
    have hysup : y ∈ (F[i]'hi).support :=
      mem_support_of_ideal_eq_span_singleton _ hU hyU (c.coord j) hidU hynb
    have hidU' : (F[i]'hi).ideal ⟨X.basicOpen t, hUt⟩
        = Ideal.span {(c.restrict hle).coord j} := by
      rw [(c.restrict hle).ideal_eq_span_coord hUt _ _
        (restrictIdeal_eq_restrict_coordIdeal_of_le hle c _ _ (hB j hg)), Finset.coe_singleton,
        Set.image_singleton]
    exact mem_primeIdealOf_of_mem_support_of_ideal_eq_span_singleton _ hUt hy' _ hidU' hysup
end FunctorialResolution.EmbeddedResolution
