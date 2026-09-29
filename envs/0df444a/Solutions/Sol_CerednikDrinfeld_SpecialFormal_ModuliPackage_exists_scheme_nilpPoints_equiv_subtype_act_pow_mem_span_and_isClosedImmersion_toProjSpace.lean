-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.ModuliPackage.exists_scheme_nilpPoints_equiv_subtype_act_pow_mem_span_and_isClosedImmersion_toProjSpace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/d3d88d17-b019-507c-a240-775c54cea554

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_PeriodMapSpec
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_scheme_represents_subgroup_ideal_and_isClosedImmersion_toProjSpace
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_cover_isIsogenyOfHeight_span_range_eq_map_of_subgroup_ideal
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_forall_act_pow_mem_span_of_isNilpotent_of_X_pow_mem
import Theorems.Thm_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_map_of_bijective
import Theorems.Thm_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_comp_map_of_field
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_X_pow_mem_span_of_hasKernelOfDegree
import Theorems.Thm_CerednikDrinfeld_FormalODModule_subst_mem_span_of_isODHom
import Theorems.Thm_CerednikDrinfeld_FormalODModule_Hom_eq_of_comp_act_pow_eq_of_hasKernelOfDegree
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isODHom_comp_eq_of_span_range_eq_of_hasKernelOfDegree
import Theorems.Thm_CerednikDrinfeld_FormalODModule_hasHeight_four_of_isIsogenyOfHeight
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_isOpenImmersion_isClosedImmersion_iff_of_isIdempotentElem_of_forall_exists_idempotent_of_finiteType
import Theorems.Thm_CerednikDrinfeld_FormalODModule_IsSpecial_of_isODHom_of_comp_eq_id
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isSpecial_of_forall_isSpecial_map_away
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_idempotent_isSpecial_map_iff
import Theorems.Thm_Localization_Away_existsUnique_forall_algebraMap_eq_of_span_eq_top
import Theorems.Thm_CerednikDrinfeld_FormalODModule_IsSpecial_map
import Theorems.Thm_MvPowerSeries_span_range_X_eq_ker_constantCoeff
import Theorems.Thm_CerednikDrinfeld_FormalODModule_hasKernelOfDegree_map
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsAdmissible_map_ringHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_scheme_nilpPoints_equiv_subtype_act_pow_mem_span_and_isClosedImmersion_toProjSpace
p2m_attr_erase "instance" "MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup HopfAlgebra.HopfIdealQuotient.instIsCocomm HopfAlgebra.HopfIdealQuotient.instBialgebra HopfAlgebra.HopfIdealQuotient.instHopfAlgebra Ideal.isHopfIdeal_bot HopfAlgebra.flat_quotient_bot HopfAlgebra.finiteType_quotient instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec HopfAlgebra.HopfIdealQuotient.comul_mk HopfAlgebra.antipodeAlgHom_apply HopfAlgebra.quotientFactorBialgHom_apply_mk HopfAlgebra.quotientBialgHom_apply HopfAlgebra.quotientLiftPoint_mk HopfAlgebra.convCompMonoidHom_apply HopfAlgebra.HopfIdealQuotient.antipode_mk HopfAlgebra.HopfIdealQuotient.counit_mk CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

namespace D4

open MvPowerSeries

variable {p : ℕ} [Fact p.Prime]

theorem natCast_p_eq_zero {k : Type} [CommRing k] (S : Type) [CommRing S] [Algebra (WittVector p k ⧸ pIdeal p (WittVector p k)) S] : (p : S) = 0 := by
  have : ((p : (WittVector p k ⧸ pIdeal p (WittVector p k)))) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk (pIdeal p (WittVector p k))) p, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl
  rw [← map_natCast (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) S) p, this, map_zero]

theorem pIdeal_eq_bot {k : Type} [CommRing k] (S : Type) [CommRing S] [Algebra (WittVector p k ⧸ pIdeal p (WittVector p k)) S] : pIdeal p S = ⊥ := by
  rw [pIdeal, natCast_p_eq_zero (k := k) S, Ideal.span_singleton_eq_bot]

noncomputable def quotEquiv {k : Type} [CommRing k] (S : Type) [CommRing S] [Algebra (WittVector p k ⧸ pIdeal p (WittVector p k)) S] : S ≃+* S ⧸ pIdeal p S :=
  (RingEquiv.quotientBot S).symm.trans (Ideal.quotEquivOfEq (pIdeal_eq_bot (k := k) S).symm)

theorem quotEquiv_apply {k : Type} [CommRing k] (S : Type) [CommRing S] [Algebra (WittVector p k ⧸ pIdeal p (WittVector p k)) S] (s : S) :
    quotEquiv (k := k) S s = Ideal.Quotient.mk (pIdeal p S) s := rfl

end D4

namespace D4

noncomputable def coverOfISupEqTop {X : Scheme} {J : Type} (U : J → X.Opens) (hU : ⨆ j, U j = ⊤) : X.OpenCover where
  I₀ := J
  X j := U j
  f j := (U j).ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, inferInstance⟩
    have hx : x ∈ (⨆ j, U j) := by rw [hU]; trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact ⟨j, ⟨x, hj⟩, rfl⟩

theorem glue_opens {X Y : Scheme} {J : Type} (U : J → X.Opens) (hU : ⨆ j, U j = ⊤)
    (g : ∀ j, (U j : Scheme) ⟶ Y)
    (hg : ∀ i j, X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ g i = X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j) ≫ g j) :
    ∃ φ : X ⟶ Y, ∀ j, (U j).ι ≫ φ = g j := by
  let 𝒰 := coverOfISupEqTop U hU
  have hcompat : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ g i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ g j := by
    intro i j
    have P := isPullback_opens_inf (U i) (U j)
    show pullback.fst (U i).ι (U j).ι ≫ g i = pullback.snd (U i).ι (U j).ι ≫ g j
    rw [← P.isoPullback_inv_fst, ← P.isoPullback_inv_snd, Category.assoc, Category.assoc, hg i j]
  exact ⟨Scheme.Cover.glueMorphisms 𝒰 g hcompat, fun j => Scheme.Cover.ι_glueMorphisms 𝒰 g hcompat j⟩

theorem glue_opens_unique {X Y : Scheme} {J : Type} (U : J → X.Opens) (hU : ⨆ j, U j = ⊤)
    (φ₁ φ₂ : X ⟶ Y) (h : ∀ j, (U j).ι ≫ φ₁ = (U j).ι ≫ φ₂) : φ₁ = φ₂ :=
  Scheme.Cover.hom_ext (coverOfISupEqTop U hU) φ₁ φ₂ h

theorem iSup_basicOpen_eq_top {S : Type} [CommRing S] {r : ℕ} (f : Fin r → S) (hf : Ideal.span (Set.range f) = ⊤) :
    (⨆ i, PrimeSpectrum.basicOpen (f i) : (Spec (CommRingCat.of S)).Opens) = ⊤ :=
  PrimeSpectrum.iSup_basicOpen_eq_top_iff.mpr hf

end D4

namespace D4
variable {p : ℕ} [Fact p.Prime]

theorem hasKernelOfDegree_act_pow_of_field {κ : Type} [Field κ] (Φk : FormalODModule p κ) (h : ℕ)
    (hΦ : Φk.HasHeight h) : ∀ d : ℕ, d ≠ 0 →
    FormalODModule.HasKernelOfDegree (Φk.act ((p : Zp2 p) ^ d)) (p ^ (h * d)) := by
  intro d
  induction d with
  | zero => intro h0; exact absurd rfl h0
  | succ d ih =>
    intro _
    rcases Nat.eq_zero_or_pos d with hd0 | hdpos
    · subst hd0
      simp only [zero_add, pow_one, mul_one] at hΦ ⊢
      exact hΦ
    · have ih' := ih (Nat.pos_iff_ne_zero.mp hdpos)
      have hc := CerednikDrinfeld.FormalODModule.HasKernelOfDegree.comp_map_of_field (RingHom.id κ) ih'
        (φ := Φk.act (p : Zp2 p)) (Φk.isLawHom_act _).1 hΦ
      rw [Series.map_ringHom_id, ← FormalODModule.act_mul, ← pow_succ, ← pow_add, ← Nat.mul_succ] at hc
      exact hc

end D4

namespace D4

open MvPowerSeries

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p]

local notation "K₀" => (WittVector p k ⧸ pIdeal p (WittVector p k))

theorem isMaximal_pIdeal : (pIdeal p (WittVector p k)).IsMaximal := by
  have h : pIdeal p (WittVector p k) = RingHom.ker (WittVector.constantCoeff : WittVector p k →+* k) :=
    (WittVector.ker_constantCoeff).symm
  rw [h]
  exact RingHom.ker_isMaximal_of_surjective _ (WittVector.constantCoeff_surjective p)

@[reducible] noncomputable def fieldK0 : Field K₀ :=
  @Ideal.Quotient.field _ _ (pIdeal p (WittVector p k)) isMaximal_pIdeal

theorem hasKernelOfDegree_act_pow_K0 (Φ : FormalODModule p K₀) (hΦ4 : Φ.HasHeight 4) (N : ℕ) (hN : N ≠ 0) :
    FormalODModule.HasKernelOfDegree (Φ.act ((p : Zp2 p) ^ N)) (p ^ (4 * N)) := by
  let g : K₀ ≃+* k := WittVector.quotientPEquiv
  have hΦk : (Φ.map g.toRingHom).HasHeight 4 := by
    show FormalODModule.HasKernelOfDegree ((Φ.map g.toRingHom).act (p : Zp2 p)) (p ^ 4)
    rw [FormalODModule.map_act]
    exact CerednikDrinfeld.FormalODModule.HasKernelOfDegree.map_of_bijective g.toRingHom g.bijective hΦ4
  have hk := hasKernelOfDegree_act_pow_of_field (Φ.map g.toRingHom) 4 hΦk N hN
  have := CerednikDrinfeld.FormalODModule.HasKernelOfDegree.map_of_bijective g.symm.toRingHom g.symm.bijective hk
  rwa [FormalODModule.map_act, Series.map_map, RingEquiv.symm_toRingHom_comp_toRingHom, Series.map_ringHom_id] at this

theorem kerAlgebra_inputs (Φ : FormalODModule p K₀) (hΦ4 : Φ.HasHeight 4) (N : ℕ) (hN : N ≠ 0) :
    Module.Finite K₀ (FormalODModule.KerAlgebra (Φ.act ((p : Zp2 p) ^ N))) ∧
    Module.Free K₀ (FormalODModule.KerAlgebra (Φ.act ((p : Zp2 p) ^ N))) ∧
    ∀ i, IsNilpotent (Ideal.Quotient.mk (Ideal.span (Set.range (Φ.act ((p : Zp2 p) ^ N)))) (MvPowerSeries.X i)) := by
  have hker := hasKernelOfDegree_act_pow_K0 Φ hΦ4 N hN
  haveI : Module.Finite K₀ (FormalODModule.KerAlgebra (Φ.act ((p : Zp2 p) ^ N))) := hker.1
  refine ⟨hker.1, ?_, ?_⟩
  · letI : Field K₀ := fieldK0
    exact Module.Free.of_divisionRing K₀ _
  obtain ⟨M, hM⟩ := CerednikDrinfeld.FormalODModule.exists_X_pow_mem_span_of_hasKernelOfDegree (Φ.act ((p : Zp2 p) ^ N))
    (Φ.isLawHom_act _).1 hker
  intro i
  exact ⟨M, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact hM i⟩

end D4

namespace D4

open MvPowerSeries

variable {p : ℕ} [Fact p.Prime]

theorem ideal_map_span_range {R' S' ι : Type} [CommRing R'] [CommRing S'] (φ : R' →+* S') (ρ : ι → R') :
    Ideal.map φ (Ideal.span (Set.range ρ)) = Ideal.span (Set.range (fun i => φ (ρ i))) := by
  rw [Ideal.map_span, ← Set.range_comp]; rfl

abbrev PZ (B₀ : Type) [CommRing B₀] (Φ : FormalODModule p B₀) (N h : ℕ) (S : Type) [CommRing S] [Algebra B₀ S]
    (I : Ideal (MvPowerSeries (Fin 2) S)) : Prop :=
  Module.Finite S (MvPowerSeries (Fin 2) S ⧸ I) ∧
            Module.Projective S (MvPowerSeries (Fin 2) S ⧸ I) ∧
            (∀ (κ : Type) [Field κ] (f : S →+* κ),
              Module.finrank κ (MvPowerSeries (Fin 2) κ ⧸ (I).map (MvPowerSeries.map f)) = p ^ h) ∧
            (∃ q : ℕ, ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) S) ^ q ∈ I) ∧
            (∀ f ∈ I, MvPowerSeries.constantCoeff f = 0) ∧
            (∀ f ∈ I, MvPowerSeries.subst (Φ.map (algebraMap B₀ S)).F.toPowerSeries f ∈
              Ideal.span
                ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) S))) ''
                    (I : Set (MvPowerSeries (Fin 2) S)) ∪
                 (MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) S))) ''
                    (I : Set (MvPowerSeries (Fin 2) S)))) ∧
            (∀ (a : Zp2 p), ∀ f ∈ I, MvPowerSeries.subst ((Φ.map (algebraMap B₀ S)).act a) f ∈ I) ∧
            (∀ f ∈ I, MvPowerSeries.subst (Φ.map (algebraMap B₀ S)).varpi f ∈ I) ∧
            (∀ j : Fin 2, (Φ.map (algebraMap B₀ S)).act ((p : Zp2 p) ^ N) j ∈ I)

theorem span_image_union_eq {R' T : Type} [CommRing R'] [CommRing T] [Algebra R' T] (A B : MvPowerSeries (Fin 2) R' →ₐ[R'] T)
    (ρ : Series R') :
    Ideal.span ((A : MvPowerSeries (Fin 2) R' → T) '' (Ideal.span (Set.range ρ) : Set (MvPowerSeries (Fin 2) R')) ∪
        (B : MvPowerSeries (Fin 2) R' → T) '' (Ideal.span (Set.range ρ) : Set (MvPowerSeries (Fin 2) R'))) =
      Ideal.span (Set.range (fun j => A (ρ j)) ∪ Set.range (fun j => B (ρ j))) := by
  rw [Ideal.span_union, Ideal.span_union]
  have hA : Ideal.span ((A : MvPowerSeries (Fin 2) R' → T) '' (Ideal.span (Set.range ρ) : Set (MvPowerSeries (Fin 2) R'))) =
      Ideal.span (Set.range (fun j => A (ρ j))) := by
    rw [← Ideal.map, show ((A : MvPowerSeries (Fin 2) R' → T)) = ⇑A.toRingHom from rfl]
    exact ideal_map_span_range A.toRingHom ρ
  have hB : Ideal.span ((B : MvPowerSeries (Fin 2) R' → T) '' (Ideal.span (Set.range ρ) : Set (MvPowerSeries (Fin 2) R'))) =
      Ideal.span (Set.range (fun j => B (ρ j))) := by
    rw [← Ideal.map, show ((B : MvPowerSeries (Fin 2) R' → T)) = ⇑B.toRingHom from rfl]
    exact ideal_map_span_range B.toRingHom ρ
  rw [hA, hB]

variable {k : Type} [Field k] [CharP k p] [PerfectRing k p]

local notation "K₀" => (WittVector p k ⧸ pIdeal p (WittVector p k))

theorem PZ_span_of_isAdmissible {Φ : FormalODModule p K₀} {L : Type} [CommRing L] [IsNoetherianRing L]
    (ι : Zp2 p →+* WittVector p k) (ψ : WittVector p k →+* L) (t : Rigidified p Φ L) (ht : t.IsAdmissible ι ψ) (n m : ℕ)
    (hn : t.n = n) (hcont : ∀ j, (t.Φbar ψ).act ((p : Zp2 p) ^ (n + m)) j ∈ Ideal.span (Set.range t.ρ)) :
    letI : Algebra K₀ (L ⧸ pIdeal p L) := (residueMap ψ).toAlgebra
    PZ K₀ Φ (n + m) (4 * n) (L ⧸ pIdeal p L) (Ideal.span (Set.range t.ρ)) := by
  letI : Algebra K₀ (L ⧸ pIdeal p L) := (residueMap ψ).toAlgebra
  have hΦ : Φ.map (algebraMap K₀ (L ⧸ pIdeal p L)) = t.Φbar ψ := rfl
  obtain ⟨hodh, hker⟩ := ht.2.2
  subst hn
  have hst := CerednikDrinfeld.FormalODModule.subst_mem_span_of_isODHom p (t.Φbar ψ) t.Xbar t.ρ hodh
  refine ⟨hker.1, hker.2.1, ?_, ?_, ?_, ?_, ?_, ?_, hcont⟩
  · intro κ _ f
    rw [ideal_map_span_range]
    exact hker.2.2 κ f
  · exact CerednikDrinfeld.FormalODModule.exists_X_pow_mem_span_of_hasKernelOfDegree t.ρ hodh.constantCoeff hker
  · intro f hf
    have hle : Ideal.span (Set.range t.ρ) ≤ RingHom.ker (constantCoeff : MvPowerSeries (Fin 2) (L ⧸ pIdeal p L) →+* _) :=
      Ideal.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hodh.constantCoeff j)
    exact hle hf
  · intro f hf
    have h3 := hst.2.2 f hf
    rw [hΦ]
    have hXl : ∀ l : Fin 2, constantCoeff ((X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) (L ⧸ pIdeal p L))) = 0 :=
      fun l => constantCoeff_X _
    have hXr : ∀ l : Fin 2, constantCoeff ((X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) (L ⧸ pIdeal p L))) = 0 :=
      fun l => constantCoeff_X _
    have e := span_image_union_eq (substAlgHom (hasSubst_of_constantCoeff_zero hXl)) (substAlgHom (hasSubst_of_constantCoeff_zero hXr)) t.ρ
    simp only [coe_substAlgHom] at e
    rw [e]
    exact h3
  · intro a f hf
    rw [hΦ]
    exact hst.1 a f hf
  · intro f hf
    rw [hΦ]
    exact hst.2.1 f hf

end D4

namespace D4

open MvPowerSeries

section H1
variable {R' : Type} [CommRing R']

theorem subst_mem_span_comp (ρ h : Series R') (hh : ∀ i, constantCoeff (h i) = 0)
    {G : MvPowerSeries (Fin 2) R'} (hG : G ∈ Ideal.span (Set.range ρ)) :
    subst h G ∈ Ideal.span (Set.range (ρ.comp h)) := by
  have ha := hasSubst_of_constantCoeff_zero hh
  have := Ideal.mem_map_of_mem (substAlgHom ha).toRingHom hG
  rw [ideal_map_span_range] at this
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, coe_substAlgHom] at this
  exact this

theorem subst_mem_of_constantCoeff_eq_zero (I : Ideal (MvPowerSeries (Fin 2) R')) (h : Series R')
    (hh : ∀ i, constantCoeff (h i) = 0) (hI : ∀ i, h i ∈ I)
    {G : MvPowerSeries (Fin 2) R'} (hG : constantCoeff G = 0) : subst h G ∈ I := by
  have ha := hasSubst_of_constantCoeff_zero hh
  have hGX : G ∈ Ideal.span (Set.range (X : Fin 2 → MvPowerSeries (Fin 2) R')) := by
    rw [MvPowerSeries.span_range_X_eq_ker_constantCoeff]; exact hG
  have := Ideal.mem_map_of_mem (substAlgHom ha).toRingHom hGX
  rw [ideal_map_span_range] at this
  have h2 : (fun i => (substAlgHom (R := R') ha).toRingHom (X i : MvPowerSeries (Fin 2) R')) = h := by
    funext i
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, coe_substAlgHom]
    exact subst_X ha i
  rw [h2] at this
  have this' : subst h G ∈ Ideal.span (Set.range h) := by
    simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, coe_substAlgHom] using this
  exact (Ideal.span_le.mpr (Set.range_subset_iff.mpr hI)) this'

end H1

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p]

local notation "K₀" => (WittVector p k ⧸ pIdeal p (WittVector p k))

theorem hasKernelOfDegree_act_pow_Φbar {Φ : FormalODModule p K₀} (hΦ4 : Φ.HasHeight 4) {L : Type} [CommRing L]
    [IsNoetherianRing L] (ψ : WittVector p k →+* L) (t : Rigidified p Φ L) (N : ℕ) (hN : N ≠ 0) :
    FormalODModule.HasKernelOfDegree ((t.Φbar ψ).act ((p : Zp2 p) ^ N)) (p ^ (4 * N)) := by
  show FormalODModule.HasKernelOfDegree ((Φ.map (residueMap ψ)).act ((p : Zp2 p) ^ N)) (p ^ (4 * N))
  rw [FormalODModule.map_act]
  exact CerednikDrinfeld.FormalODModule.hasKernelOfDegree_map (residueMap ψ) _ (Φ.isLawHom_act _).1
    (hasKernelOfDegree_act_pow_K0 Φ hΦ4 N hN)

theorem span_eq_of_isIsomorphic {Φ : FormalODModule p K₀} (hΦ4 : Φ.HasHeight 4) {L : Type} [CommRing L]
    [IsNoetherianRing L] (ι : Zp2 p →+* WittVector p k) (ψ : WittVector p k →+* L) (t t' : Rigidified p Φ L)
    (ht : t.IsAdmissible ι ψ) (ht' : t'.IsAdmissible ι ψ) (hn : t.n = t'.n) (hiso : t.IsIsomorphic t') :
    Ideal.span (Set.range t.ρ) = Ideal.span (Set.range t'.ρ) := by
  obtain ⟨u, v, m, hu, hv, hvu, huv, h⟩ := hiso
  rw [hn] at h
  have hub : FormalODModule.IsODHom t.Xbar t'.Xbar (u.map (Ideal.Quotient.mk (pIdeal p L))) := hu.map _
  have hvb : FormalODModule.IsODHom t'.Xbar t.Xbar (v.map (Ideal.Quotient.mk (pIdeal p L))) := hv.map _
  have hρ := ht.2.2.1
  have hρ' := ht'.2.2.1
  have hα : FormalODModule.IsODHom (t.Φbar ψ) t'.Xbar ((u.map (Ideal.Quotient.mk (pIdeal p L))).comp t.ρ) := hub.comp hρ

  have e1 : ((u.map (Ideal.Quotient.mk (pIdeal p L))).comp t.ρ).comp ((t.Φbar ψ).act ((p : Zp2 p) ^ (m + t'.n))) =
      t'.ρ.comp ((t.Φbar ψ).act ((p : Zp2 p) ^ (m + t'.n))) := by
    rw [hα.2.1, hρ'.2.1]
    exact h
  have heq : (u.map (Ideal.Quotient.mk (pIdeal p L))).comp t.ρ = t'.ρ := by
    rcases Nat.eq_zero_or_pos (m + t'.n) with h0 | hpos
    · rw [h0, pow_zero, FormalODModule.act_one, Series.comp_id, Series.comp_id] at e1
      exact e1
    · have hk := hasKernelOfDegree_act_pow_Φbar hΦ4 ψ t (m + t'.n) hpos.ne'
      have := CerednikDrinfeld.FormalODModule.Hom.eq_of_comp_act_pow_eq_of_hasKernelOfDegree (m + t'.n) _ hk
        ⟨_, hα⟩ ⟨_, hρ'⟩ e1
      exact congrArg FormalODModule.Hom.toSeries this
  rw [← heq]
  apply le_antisymm
  ·
    have hvu' : (v.map (Ideal.Quotient.mk (pIdeal p L))).comp (u.map (Ideal.Quotient.mk (pIdeal p L))) = Series.id _ := by
      rw [← Series.map_comp _ _ _ hu.constantCoeff, hvu, Series.map_id]
    have hback : t.ρ = (v.map (Ideal.Quotient.mk (pIdeal p L))).comp ((u.map (Ideal.Quotient.mk (pIdeal p L))).comp t.ρ) := by
      rw [← Series.comp_assoc _ _ _ hub.constantCoeff hρ.constantCoeff, hvu', Series.id_comp _ hρ.constantCoeff]
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    have hmem := subst_mem_of_constantCoeff_eq_zero
      (Ideal.span (Set.range ((u.map (Ideal.Quotient.mk (pIdeal p L))).comp t.ρ)))
      ((u.map (Ideal.Quotient.mk (pIdeal p L))).comp t.ρ)
      (Series.constantCoeff_comp hub.constantCoeff hρ.constantCoeff)
      (fun i => Ideal.subset_span (Set.mem_range_self i)) (hvb.constantCoeff j)
    have hj : t.ρ j = ((v.map (Ideal.Quotient.mk (pIdeal p L))).comp ((u.map (Ideal.Quotient.mk (pIdeal p L))).comp t.ρ)) j :=
      congrFun hback j
    show t.ρ j ∈ _
    rw [hj]
    exact hmem
  · refine Ideal.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    exact subst_mem_of_constantCoeff_eq_zero _ t.ρ hρ.constantCoeff (fun i => Ideal.subset_span (Set.mem_range_self i)) (hub.constantCoeff j)

end D4

namespace D4

open MvPowerSeries

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p]

local notation "K₀" => (WittVector p k ⧸ pIdeal p (WittVector p k))

noncomputable abbrev ψof (S : Type) [CommRing S] [Algebra K₀ S] : WittVector p k →+* S :=
  (algebraMap K₀ S).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))

theorem algebraMap_quot_eq_residueMap (S : Type) [CommRing S] [Algebra K₀ S] :
    (algebraMap K₀ (S ⧸ pIdeal p S)) = residueMap (ψof S) := by
  apply Ideal.Quotient.ringHom_ext
  ext w
  rfl

theorem map_algebraMap_quot_eq_Φbar {Φ : FormalODModule p K₀} (S : Type) [CommRing S] [Algebra K₀ S] (t : Rigidified p Φ S) :
    Φ.map (algebraMap K₀ (S ⧸ pIdeal p S)) = t.Φbar (ψof S) := by
  rw [algebraMap_quot_eq_residueMap]

theorem PZ_quot_of_isAdmissible {Φ : FormalODModule p K₀} (hΦ4 : Φ.HasHeight 4) {L : Type} [CommRing L] [IsNoetherianRing L]
    [Algebra K₀ L] (ι : Zp2 p →+* WittVector p k) (t : Rigidified p Φ L) (ht : t.IsAdmissible ι (ψof L)) (n m : ℕ)
    (hn : t.n = n) (hcont : ∀ j, (t.Φbar (ψof L)).act ((p : Zp2 p) ^ (n + m)) j ∈ Ideal.span (Set.range t.ρ)) :
    PZ K₀ Φ (n + m) (4 * n) (L ⧸ pIdeal p L) (Ideal.span (Set.range t.ρ)) := by
  have key := PZ_span_of_isAdmissible ι (ψof L) t ht n m hn hcont

  have hinst : (Ideal.Quotient.algebra K₀ : Algebra K₀ (L ⧸ pIdeal p L)) = (residueMap (ψof L)).toAlgebra := by
    apply Algebra.algebra_ext
    intro r
    exact congrFun (congrArg DFunLike.coe (algebraMap_quot_eq_residueMap (p := p) (k := k) L)) r
  rw [show @PZ p _ K₀ _ Φ (n + m) (4 * n) (L ⧸ pIdeal p L) _ (Ideal.Quotient.algebra K₀) (Ideal.span (Set.range t.ρ)) =
      @PZ p _ K₀ _ Φ (n + m) (4 * n) (L ⧸ pIdeal p L) _ (residueMap (ψof L)).toAlgebra (Ideal.span (Set.range t.ρ)) from by rw [hinst]]
  exact key

end D4

namespace D4

open MvPowerSeries

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p]

local notation "K₀" => (WittVector p k ⧸ pIdeal p (WittVector p k))

noncomputable def quotAlgEquiv (L : Type) [CommRing L] [Algebra K₀ L] : L ≃ₐ[K₀] (L ⧸ pIdeal p L) :=
  AlgEquiv.ofRingEquiv (f := quotEquiv (k := k) L) (fun r => rfl)

theorem quotAlgEquiv_apply (L : Type) [CommRing L] [Algebra K₀ L] (x : L) :
    quotAlgEquiv (k := k) L x = Ideal.Quotient.mk (pIdeal p L) x := rfl

theorem quotAlgEquiv_symm_mk (L : Type) [CommRing L] [Algebra K₀ L] (x : L) :
    (quotAlgEquiv (k := k) L).symm (Ideal.Quotient.mk (pIdeal p L) x) = x :=
  (quotAlgEquiv (k := k) L).symm_apply_apply x

noncomputable def kerIdeal {Φ : FormalODModule p K₀} {L : Type} [CommRing L] [Algebra K₀ L] (t : Rigidified p Φ L) :
    Ideal (MvPowerSeries (Fin 2) L) :=
  (Ideal.span (Set.range t.ρ)).map (MvPowerSeries.map (quotAlgEquiv (k := k) L).symm.toRingEquiv.toRingHom)

noncomputable def pointOfTriple {Φ : FormalODModule p K₀} (hΦ4 : Φ.HasHeight 4) (ι : Zp2 p →+* WittVector p k) (n m : ℕ)
    {H : Scheme.{0}} {q : H ⟶ Spec (CommRingCat.of K₀)}
    (pt : ∀ (S : Type) [CommRing S] [Algebra K₀ S],
      {I : Ideal (MvPowerSeries (Fin 2) S) // PZ K₀ Φ (n + m) (4 * n) S I} ≃
        {g : Spec (CommRingCat.of S) ⟶ H // g ≫ q = Spec.map (CommRingCat.ofHom (algebraMap K₀ S))})
    (hmap : ∀ (S S' : Type) [CommRing S] [CommRing S'] [Algebra K₀ S] [Algebra K₀ S'] (φ : S →ₐ[K₀] S')
      (I : {I : Ideal (MvPowerSeries (Fin 2) S) // PZ K₀ Φ (n + m) (4 * n) S I}),
      PZ K₀ Φ (n + m) (4 * n) S' (I.1.map (MvPowerSeries.map (φ : S →+* S'))))
    {L : Type} [CommRing L] [IsNoetherianRing L] [Algebra K₀ L]
    (t : Rigidified p Φ L) (ht : t.IsAdmissible ι (ψof L)) (hn : t.n = n)
    (hcont : ∀ j, (t.Φbar (ψof L)).act ((p : Zp2 p) ^ (n + m)) j ∈ Ideal.span (Set.range t.ρ)) :
    {g : Spec (CommRingCat.of L) ⟶ H // g ≫ q = Spec.map (CommRingCat.ofHom (algebraMap K₀ L))} :=
  pt L ⟨kerIdeal t, hmap _ _ (quotAlgEquiv (k := k) L).symm.toAlgHom
    ⟨Ideal.span (Set.range t.ρ), PZ_quot_of_isAdmissible hΦ4 ι t ht n m hn hcont⟩⟩

end D4

namespace D4

open MvPowerSeries

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p]

local notation "K₀" => (WittVector p k ⧸ pIdeal p (WittVector p k))

theorem span_range_map_eq_map {R' S' : Type} [CommRing R'] [CommRing S'] (f : R' →+* S') (ρ : Series R') :
    Ideal.span (Set.range (ρ.map f)) = (Ideal.span (Set.range ρ)).map (MvPowerSeries.map f) := by
  rw [ideal_map_span_range]; rfl

theorem pointOfTriple_congr {Φ : FormalODModule p K₀} (hΦ4 : Φ.HasHeight 4) (ι : Zp2 p →+* WittVector p k) (n m : ℕ)
    {H : Scheme.{0}} {q : H ⟶ Spec (CommRingCat.of K₀)}
    (pt : ∀ (S : Type) [CommRing S] [Algebra K₀ S],
      {I : Ideal (MvPowerSeries (Fin 2) S) // PZ K₀ Φ (n + m) (4 * n) S I} ≃
        {g : Spec (CommRingCat.of S) ⟶ H // g ≫ q = Spec.map (CommRingCat.ofHom (algebraMap K₀ S))})
    (hmap : ∀ (S S' : Type) [CommRing S] [CommRing S'] [Algebra K₀ S] [Algebra K₀ S'] (φ : S →ₐ[K₀] S')
      (I : {I : Ideal (MvPowerSeries (Fin 2) S) // PZ K₀ Φ (n + m) (4 * n) S I}),
      PZ K₀ Φ (n + m) (4 * n) S' (I.1.map (MvPowerSeries.map (φ : S →+* S'))))
    {L : Type} [CommRing L] [IsNoetherianRing L] [Algebra K₀ L]
    (t t' : Rigidified p Φ L) (ht : t.IsAdmissible ι (ψof L)) (ht' : t'.IsAdmissible ι (ψof L)) (hn : t.n = n) (hn' : t'.n = n)
    (hcont : ∀ j, (t.Φbar (ψof L)).act ((p : Zp2 p) ^ (n + m)) j ∈ Ideal.span (Set.range t.ρ))
    (hcont' : ∀ j, (t'.Φbar (ψof L)).act ((p : Zp2 p) ^ (n + m)) j ∈ Ideal.span (Set.range t'.ρ))
    (hiso : t.IsIsomorphic t') :
    (pointOfTriple hΦ4 ι n m pt hmap t ht hn hcont).1 = (pointOfTriple hΦ4 ι n m pt hmap t' ht' hn' hcont').1 := by
  have hker : kerIdeal (k := k) t = kerIdeal t' := by
    unfold kerIdeal
    rw [span_eq_of_isIsomorphic hΦ4 ι (ψof L) t t' ht ht' (hn.trans hn'.symm) hiso]
  unfold pointOfTriple
  congr 2
  exact Subtype.ext hker

theorem quotAlgEquiv_symm_comp_reduceMap {L L' : Type} [CommRing L] [CommRing L'] [Algebra K₀ L] [Algebra K₀ L']
    (g : L →ₐ[K₀] L') :
    (quotAlgEquiv (k := k) L').symm.toRingEquiv.toRingHom.comp (reduceMap (p := p) (g : L →+* L')) =
      (g : L →+* L').comp (quotAlgEquiv (k := k) L).symm.toRingEquiv.toRingHom := by
  apply Ideal.Quotient.ringHom_ext
  ext x
  show (quotAlgEquiv (k := k) L').symm (Ideal.Quotient.mk (pIdeal p L') (g x)) = g ((quotAlgEquiv (k := k) L).symm (Ideal.Quotient.mk (pIdeal p L) x))
  rw [quotAlgEquiv_symm_mk, quotAlgEquiv_symm_mk]

theorem kerIdeal_map {Φ : FormalODModule p K₀} {L L' : Type} [CommRing L] [CommRing L'] [Algebra K₀ L] [Algebra K₀ L']
    (g : L →ₐ[K₀] L') (t : Rigidified p Φ L) :
    kerIdeal (k := k) (t.map (g : L →+* L')) = (kerIdeal (k := k) t).map (MvPowerSeries.map (g : L →+* L')) := by
  unfold kerIdeal
  rw [Rigidified.map_ρ, span_range_map_eq_map, Ideal.map_map, Ideal.map_map]
  congr 1
  rw [← MvPowerSeries.map_comp, ← MvPowerSeries.map_comp, quotAlgEquiv_symm_comp_reduceMap]

theorem pointOfTriple_map {Φ : FormalODModule p K₀} (hΦ4 : Φ.HasHeight 4) (ι : Zp2 p →+* WittVector p k) (n m : ℕ)
    {H : Scheme.{0}} {q : H ⟶ Spec (CommRingCat.of K₀)}
    (pt : ∀ (S : Type) [CommRing S] [Algebra K₀ S],
      {I : Ideal (MvPowerSeries (Fin 2) S) // PZ K₀ Φ (n + m) (4 * n) S I} ≃
        {g : Spec (CommRingCat.of S) ⟶ H // g ≫ q = Spec.map (CommRingCat.ofHom (algebraMap K₀ S))})
    (hmap : ∀ (S S' : Type) [CommRing S] [CommRing S'] [Algebra K₀ S] [Algebra K₀ S'] (φ : S →ₐ[K₀] S')
      (I : {I : Ideal (MvPowerSeries (Fin 2) S) // PZ K₀ Φ (n + m) (4 * n) S I}),
      PZ K₀ Φ (n + m) (4 * n) S' (I.1.map (MvPowerSeries.map (φ : S →+* S'))))
    (hnat : ∀ (S S' : Type) [CommRing S] [CommRing S'] [Algebra K₀ S] [Algebra K₀ S'] (φ : S →ₐ[K₀] S')
      (I : {I : Ideal (MvPowerSeries (Fin 2) S) // PZ K₀ Φ (n + m) (4 * n) S I}),
      (pt S' ⟨I.1.map (MvPowerSeries.map (φ : S →+* S')), hmap S S' φ I⟩).1 =
        Spec.map (CommRingCat.ofHom (φ : S →+* S')) ≫ (pt S I).1)
    {L L' : Type} [CommRing L] [IsNoetherianRing L] [Algebra K₀ L] [CommRing L'] [IsNoetherianRing L'] [Algebra K₀ L']
    (g : L →ₐ[K₀] L')
    (t : Rigidified p Φ L) (ht : t.IsAdmissible ι (ψof L)) (hn : t.n = n)
    (hcont : ∀ j, (t.Φbar (ψof L)).act ((p : Zp2 p) ^ (n + m)) j ∈ Ideal.span (Set.range t.ρ))
    (ht' : (t.map (g : L →+* L')).IsAdmissible ι (ψof L')) (hn' : (t.map (g : L →+* L')).n = n)
    (hcont' : ∀ j, ((t.map (g : L →+* L')).Φbar (ψof L')).act ((p : Zp2 p) ^ (n + m)) j ∈ Ideal.span (Set.range (t.map (g : L →+* L')).ρ)) :
    (pointOfTriple hΦ4 ι n m pt hmap (t.map (g : L →+* L')) ht' hn' hcont').1 =
      Spec.map (CommRingCat.ofHom (g : L →+* L')) ≫ (pointOfTriple hΦ4 ι n m pt hmap t ht hn hcont).1 := by
  unfold pointOfTriple
  rw [← hnat L L' g]
  congr 2
  exact Subtype.ext (kerIdeal_map g t)

end D4

namespace D4

open MvPowerSeries

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p]

local notation "K₀" => (WittVector p k ⧸ pIdeal p (WittVector p k))

theorem algHom_comp_ψof {L L' : Type} [CommRing L] [CommRing L'] [Algebra K₀ L] [Algebra K₀ L'] (g : L →ₐ[K₀] L') :
    (g : L →+* L').comp (ψof (p := p) (k := k) L) = ψof (p := p) (k := k) L' := by
  show ((g : L →+* L').comp (algebraMap K₀ L)).comp _ = _
  rw [AlgHom.comp_algebraMap]

theorem isAdmissible_map_alg {Φ : FormalODModule p K₀} (ι : Zp2 p →+* WittVector p k) {L L' : Type} [CommRing L]
    [IsNoetherianRing L] [CommRing L'] [Algebra K₀ L] [Algebra K₀ L'] (g : L →ₐ[K₀] L') (t : Rigidified p Φ L)
    (ht : t.IsAdmissible ι (ψof L)) : (t.map (g : L →+* L')).IsAdmissible ι (ψof L') := by
  rw [← algHom_comp_ψof g]
  exact Rigidified.IsAdmissible.map_ringHom ι (ψof L) (g : L →+* L') t ht

theorem Φbar_map_alg {Φ : FormalODModule p K₀} {L L' : Type} [CommRing L] [CommRing L'] [Algebra K₀ L] [Algebra K₀ L']
    (g : L →ₐ[K₀] L') (t : Rigidified p Φ L) :
    (t.map (g : L →+* L')).Φbar (ψof L') = (t.Φbar (ψof L)).map (reduceMap (g : L →+* L')) := by
  rw [← algHom_comp_ψof g, Rigidified.Φbar_map]

theorem hcont_map_alg {Φ : FormalODModule p K₀} {L L' : Type} [CommRing L] [CommRing L'] [Algebra K₀ L] [Algebra K₀ L']
    (g : L →ₐ[K₀] L') (t : Rigidified p Φ L) (e : ℕ)
    (hcont : ∀ j, (t.Φbar (ψof L)).act ((p : Zp2 p) ^ e) j ∈ Ideal.span (Set.range t.ρ)) :
    ∀ j, ((t.map (g : L →+* L')).Φbar (ψof L')).act ((p : Zp2 p) ^ e) j ∈ Ideal.span (Set.range (t.map (g : L →+* L')).ρ) := by
  intro j
  rw [Φbar_map_alg, Rigidified.map_ρ, FormalODModule.map_act, span_range_map_eq_map]
  exact Ideal.mem_map_of_mem _ (hcont j)

noncomputable def awayRightAlg {S : Type} [CommRing S] [Algebra K₀ S] (f g : S) (P : Type) [CommRing P] [Algebra S P]
    [Algebra K₀ P] [IsScalarTower K₀ S P] [IsLocalization.Away (f * g) P] : Localization.Away f →ₐ[K₀] P :=
  { toRingHom := IsLocalization.Away.awayToAwayRight f g
    commutes' := fun r => by
      show IsLocalization.Away.awayToAwayRight f g (algebraMap K₀ (Localization.Away f) r) = algebraMap K₀ P r
      rw [IsScalarTower.algebraMap_apply K₀ S (Localization.Away f) r, IsLocalization.Away.awayToAwayRight_eq,
        ← IsScalarTower.algebraMap_apply K₀ S P r] }

theorem awayRightAlg_coe {S : Type} [CommRing S] [Algebra K₀ S] (f g : S) (P : Type) [CommRing P] [Algebra S P]
    [Algebra K₀ P] [IsScalarTower K₀ S P] [IsLocalization.Away (f * g) P] :
    (awayRightAlg (p := p) (k := k) f g P : Localization.Away f →+* P) = IsLocalization.Away.awayToAwayRight f g := rfl

theorem awayRightAlg_comp_algebraMap {S : Type} [CommRing S] [Algebra K₀ S] (f g : S) (P : Type) [CommRing P] [Algebra S P]
    [Algebra K₀ P] [IsScalarTower K₀ S P] [IsLocalization.Away (f * g) P] :
    (awayRightAlg (p := p) (k := k) f g P : Localization.Away f →+* P).comp (algebraMap S (Localization.Away f)) = algebraMap S P :=
  RingHom.ext fun a => IsLocalization.Away.awayToAwayRight_eq f g a

end D4

namespace D4

open MvPowerSeries

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p]

local notation "K₀" => (WittVector p k ⧸ pIdeal p (WittVector p k))

theorem isIsomorphic_of_span_eq {Φ : FormalODModule p K₀} (ι : Zp2 p →+* WittVector p k) {L : Type} [CommRing L]
    [IsNoetherianRing L] [Algebra K₀ L] (t t' : Rigidified p Φ L)
    (ht : t.IsAdmissible ι (ψof L)) (ht' : t'.IsAdmissible ι (ψof L)) (hn : t.n = t'.n)
    (hI : Ideal.span (Set.range t.ρ) = Ideal.span (Set.range t'.ρ)) : t.IsIsomorphic t' := by
  obtain ⟨ub, vb, hub, hvb, hvu, huv, huρ, hvρ⟩ :=
    CerednikDrinfeld.FormalODModule.exists_isODHom_comp_eq_of_span_range_eq_of_hasKernelOfDegree p (t.Φbar (ψof L)) t.Xbar t'.Xbar
      t.ρ t'.ρ ht.2.2.1 ht'.2.2.1 ht.2.2.2 hI

  let s : (L ⧸ pIdeal p L) →+* L := (quotEquiv (k := k) L).symm.toRingHom
  have hsm : (Ideal.Quotient.mk (pIdeal p L)).comp s = RingHom.id _ := by
    ext x
    show quotEquiv (k := k) L ((quotEquiv (k := k) L).symm (Ideal.Quotient.mk (pIdeal p L) x)) = Ideal.Quotient.mk (pIdeal p L) x
    exact (quotEquiv (k := k) L).apply_symm_apply _
  have hms : s.comp (Ideal.Quotient.mk (pIdeal p L)) = RingHom.id _ := by
    ext y
    show (quotEquiv (k := k) L).symm (Ideal.Quotient.mk (pIdeal p L) y) = y
    rw [← quotEquiv_apply (k := k) L y, RingEquiv.symm_apply_apply]
  have hX : ∀ (tt : Rigidified p Φ L), tt.Xbar.map s = tt.X := fun tt => by
    show (tt.X.map (Ideal.Quotient.mk (pIdeal p L))).map s = tt.X
    rw [FormalODModule.map_map, hms, FormalODModule.map_id]
  refine ⟨ub.map s, vb.map s, 0, ?_, ?_, ?_, ?_, ?_⟩
  · have := hub.map s; rwa [hX t, hX t'] at this
  · have := hvb.map s; rwa [hX t, hX t'] at this
  · rw [← Series.map_comp s _ _ hub.constantCoeff, hvu, Series.map_id]
  · rw [← Series.map_comp s _ _ hvb.constantCoeff, huv, Series.map_id]
  · rw [Series.map_map, hsm, Series.map_ringHom_id, zero_add, zero_add, hn, huρ]

end D4

namespace D4

open MvPowerSeries

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p]

local notation "K₀" => (WittVector p k ⧸ pIdeal p (WittVector p k))

def SpecialAt (Φ : FormalODModule p K₀) (ι : Zp2 p →+* WittVector p k) (B : Type) [CommRing B] [Algebra K₀ B]
    (I : Ideal (MvPowerSeries (Fin 2) B)) : Prop :=
  ∀ (B' : Type) [CommRing B'] [IsNoetherianRing B'] [Algebra K₀ B'] (φ : B →ₐ[K₀] B')
    (Y : FormalODModule p B') (ρ : Series B'),
    FormalODModule.IsODHom (Φ.map (algebraMap K₀ B')) Y ρ →
    Ideal.span (Set.range ρ) = I.map (MvPowerSeries.map (φ : B →+* B')) →
    Y.IsSpecial (structureMap ι (ψof B'))

section Witness

noncomputable def awayLeftAlg {S : Type} [CommRing S] [Algebra K₀ S] (f g : S) (P : Type) [CommRing P] [Algebra S P]
    [Algebra K₀ P] [IsScalarTower K₀ S P] [IsLocalization.Away (g * f) P] : Localization.Away f →ₐ[K₀] P :=
  { toRingHom := IsLocalization.Away.awayToAwayLeft f g
    commutes' := fun r => by
      show IsLocalization.Away.awayToAwayLeft f g (algebraMap K₀ (Localization.Away f) r) = algebraMap K₀ P r
      rw [IsScalarTower.algebraMap_apply K₀ S (Localization.Away f) r, IsLocalization.Away.awayToAwayLeft_eq,
        ← IsScalarTower.algebraMap_apply K₀ S P r] }

private noncomputable def _root_.D4.liftAlg {S : Type} [CommRing S] [Algebra K₀ S] (f : S) {T : Type} [CommRing T] [Algebra K₀ T]
    (θ : S →ₐ[K₀] T) (hf : IsUnit (θ f)) : Localization.Away f →ₐ[K₀] T :=
  { toRingHom := IsLocalization.Away.lift f (g := (θ : S →+* T)) hf
    commutes' := fun r => by
      show IsLocalization.Away.lift f hf (algebraMap K₀ (Localization.Away f) r) = algebraMap K₀ T r
      rw [IsScalarTower.algebraMap_apply K₀ S (Localization.Away f) r, IsLocalization.Away.lift_eq]
      exact θ.commutes r }

p2m_export "D4" "liftAlg"
theorem liftAlg_algebraMap {S : Type} [CommRing S] [Algebra K₀ S] (f : S) {T : Type} [CommRing T] [Algebra K₀ T]
    (θ : S →ₐ[K₀] T) (hf : IsUnit (θ f)) (s : S) : liftAlg f θ hf (algebraMap S (Localization.Away f) s) = θ s :=
  IsLocalization.Away.lift_eq f hf s

theorem idem_eq_of_forall_iff {S : Type} [CommRing S] [IsNoetherianRing S] [Algebra K₀ S] (ε₁ ε₂ : S)
    (h₁ : IsIdempotentElem ε₁) (h₂ : IsIdempotentElem ε₂)
    (h : ∀ (T : Type) [CommRing T] [IsNoetherianRing T] [Algebra K₀ T] (μ : S →ₐ[K₀] T), μ ε₁ = 1 ↔ μ ε₂ = 1) :
    ε₁ = ε₂ := by

  have key : ∀ (a b : S), IsIdempotentElem b →
      (∀ (T : Type) [CommRing T] [IsNoetherianRing T] [Algebra K₀ T] (μ : S →ₐ[K₀] T), μ b = 1 → μ a = 1) → a * b = b := by
    intro a b hb hab
    let J : Ideal S := Ideal.span {1 - b}
    have hμb : Ideal.Quotient.mkₐ K₀ J b = 1 := by
      rw [Ideal.Quotient.mkₐ_eq_mk, ← (Ideal.Quotient.mk J).map_one, Ideal.Quotient.eq, Ideal.mem_span_singleton]
      exact ⟨-1, by ring⟩
    have hμa := hab (S ⧸ J) (Ideal.Quotient.mkₐ K₀ J) hμb
    rw [Ideal.Quotient.mkₐ_eq_mk, ← (Ideal.Quotient.mk J).map_one, Ideal.Quotient.eq, Ideal.mem_span_singleton] at hμa
    obtain ⟨c, hc⟩ := hμa
    have : a = 1 + (1 - b) * c := by linear_combination hc
    rw [this, add_mul, one_mul, mul_right_comm, sub_mul, one_mul, hb.eq, sub_self, zero_mul, add_zero]
  have e12 : ε₁ * ε₂ = ε₂ := key ε₁ ε₂ h₂ fun T _ _ _ μ hμ => (h T μ).mpr hμ
  have e21 : ε₂ * ε₁ = ε₁ := key ε₂ ε₁ h₁ fun T _ _ _ μ hμ => (h T μ).mp hμ
  rw [← e21, mul_comm, e12]

omit [Fact p.Prime] [CharP k p] [PerfectRing k p] in

theorem isNoetherianRing_of_isField {R : Type} [CommRing R] (hR : IsField R) : IsNoetherianRing R := by
  refine (isNoetherianRing_iff_ideal_fg R).mpr fun J => ?_
  by_cases h : J = ⊥
  · rw [h]; exact Submodule.fg_bot
  · obtain ⟨a, haJ, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
    obtain ⟨b, hb⟩ := hR.mul_inv_cancel ha0
    have : J = ⊤ := Ideal.eq_top_of_isUnit_mem J haJ (isUnit_iff_exists_inv.mpr ⟨b, hb⟩)
    rw [this]
    exact ⟨{1}, by simp⟩

theorem exists_idempotent_specialAt_iff {Φ : FormalODModule p K₀} (hΦ4 : Φ.HasHeight 4) (ι : Zp2 p →+* WittVector p k) (n m : ℕ)
    (hmap : ∀ (S S' : Type) [CommRing S] [CommRing S'] [Algebra K₀ S] [Algebra K₀ S'] (φ : S →ₐ[K₀] S')
      (I : {I : Ideal (MvPowerSeries (Fin 2) S) // PZ K₀ Φ (n + m) (4 * n) S I}),
      PZ K₀ Φ (n + m) (4 * n) S' (I.1.map (MvPowerSeries.map (φ : S →+* S'))))
    (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra K₀ B]
    (I : {I : Ideal (MvPowerSeries (Fin 2) B) // PZ K₀ Φ (n + m) (4 * n) B I}) :
    ∃ e : B, IsIdempotentElem e ∧ ∀ (B' : Type) [CommRing B'] [Algebra K₀ B'] (φ : B →ₐ[K₀] B'),
      SpecialAt Φ ι B' (I.1.map (MvPowerSeries.map (φ : B →+* B'))) ↔ φ e = 1 := by
  obtain ⟨hfin, hproj, hrank, hnil, hunit, hmul, hact, hvarpi, -⟩ := I.2
  have hpB : IsNilpotent (p : B) := ⟨1, by rw [pow_one]; exact natCast_p_eq_zero (k := k) B⟩

  obtain ⟨r, g, hg, hloc⟩ :=
    CerednikDrinfeld.FormalODModule.exists_cover_isIsogenyOfHeight_span_range_eq_map_of_subgroup_ideal p hpB
      (Φ.map (algebraMap K₀ B)) I.1 (4 * n) hfin hproj hrank hnil hunit hmul hact hvarpi
  choose Y ρ hY hspanY using hloc

  have hpL : ∀ i : Fin r, IsNilpotent (p : Localization.Away (g i)) := fun i =>
    ⟨1, by rw [pow_one]; exact natCast_p_eq_zero (k := k) _⟩
  have hE := fun i : Fin r => CerednikDrinfeld.FormalODModule.exists_idempotent_isSpecial_map_iff p (hpL i)
    ((ψof (Localization.Away (g i))).comp ι) (Y i)
  choose e he hspec using hE

  have present : ∀ (i : Fin r) (T : Type) [CommRing T] [Algebra K₀ T] (lam : Localization.Away (g i) →ₐ[K₀] T),
      FormalODModule.IsODHom (Φ.map (algebraMap K₀ T)) ((Y i).map (lam : _ →+* T)) ((ρ i).map (lam : _ →+* T)) ∧
      Ideal.span (Set.range ((ρ i).map (lam : _ →+* T))) =
        I.1.map (MvPowerSeries.map ((lam : _ →+* T).comp (algebraMap B (Localization.Away (g i))))) := by
    intro i T _ _ lam
    constructor
    · have h := (hY i).1.map (lam : _ →+* T)
      rw [FormalODModule.map_map, FormalODModule.map_map] at h
      have hc : ((lam : _ →+* T).comp (algebraMap B (Localization.Away (g i)))).comp (algebraMap K₀ B) = algebraMap K₀ T := by
        rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq K₀ B (Localization.Away (g i))]
        exact lam.comp_algebraMap
      rwa [hc] at h
    · rw [span_range_map_eq_map, hspanY i, Ideal.map_map, ← MvPowerSeries.map_comp]

  have hspec' : ∀ (i : Fin r) (T : Type) [CommRing T] [Algebra K₀ T] (lam : Localization.Away (g i) →ₐ[K₀] T),
      ((Y i).map (lam : _ →+* T)).IsSpecial ((ψof T).comp ι) ↔ (lam : _ →+* T) (e i) = 1 := by
    intro i T _ _ lam
    have h := hspec i T (lam : _ →+* T)
    rw [← RingHom.comp_assoc, algHom_comp_ψof lam] at h
    exact h

  have transfer : ∀ (i : Fin r) (T : Type) [CommRing T] [IsNoetherianRing T] [Algebra K₀ T]
      (lam : Localization.Away (g i) →ₐ[K₀] T) (Y' : FormalODModule p T) (ρ' : Series T),
      FormalODModule.IsODHom (Φ.map (algebraMap K₀ T)) Y' ρ' →
      Ideal.span (Set.range ρ') =
        I.1.map (MvPowerSeries.map ((lam : _ →+* T).comp (algebraMap B (Localization.Away (g i))))) →
      (Y'.IsSpecial ((ψof T).comp ι) ↔ (lam : _ →+* T) (e i) = 1) := by
    intro i T _ _ _ lam Y' ρ' hρ' hsp'
    obtain ⟨h1, h2⟩ := present i T lam
    have hK0 : FormalODModule.HasKernelOfDegree (ρ i) (p ^ (4 * n)) := (hY i).2
    have hc0 : ∀ j, MvPowerSeries.constantCoeff (ρ i j) = 0 := fun j => (hY i).1.constantCoeff j
    have hker : FormalODModule.HasKernelOfDegree ((ρ i).map (lam : _ →+* T)) (p ^ (4 * n)) :=
      @CerednikDrinfeld.FormalODModule.hasKernelOfDegree_map (Localization.Away (g i)) T _ _ _ (lam : _ →+* T) (ρ i)
        hc0 (p ^ (4 * n)) hK0
    have q := @CerednikDrinfeld.FormalODModule.exists_isODHom_comp_eq_of_span_range_eq_of_hasKernelOfDegree p _ T _ _
        (Φ.map (algebraMap K₀ T)) ((Y i).map (lam : _ →+* T)) Y' ((ρ i).map (lam : _ →+* T)) ρ' h1 hρ' (p ^ (4 * n)) hker
    obtain ⟨u, v, hu, hv, hvu, huv, -, -⟩ := q (h2.trans hsp'.symm)
    constructor
    · intro hY'
      exact (hspec' i T lam).mp
        (CerednikDrinfeld.FormalODModule.IsSpecial.of_isODHom_of_comp_eq_id _ Y' _ v u hv hu huv hvu hY')
    · intro h
      exact CerednikDrinfeld.FormalODModule.IsSpecial.of_isODHom_of_comp_eq_id _ _ Y' u v hu hv hvu huv
        ((hspec' i T lam).mpr h)

  have hsame : ∀ (i j : Fin r) (T : Type) [CommRing T] [IsNoetherianRing T] [Algebra K₀ T]
      (μ : Localization.Away (g i * g j) →ₐ[K₀] T),
      μ (awayRightAlg (p := p) (k := k) (g i) (g j) (Localization.Away (g i * g j)) (e i)) = 1 ↔
      μ (awayLeftAlg (p := p) (k := k) (g j) (g i) (Localization.Away (g i * g j)) (e j)) = 1 := by
    intro i j T _ _ _ μ
    let lamI : Localization.Away (g i) →ₐ[K₀] T := μ.comp (awayRightAlg (g i) (g j) (Localization.Away (g i * g j)))
    let lamJ : Localization.Away (g j) →ₐ[K₀] T := μ.comp (awayLeftAlg (g j) (g i) (Localization.Away (g i * g j)))
    obtain ⟨hJ1, hJ2⟩ := present j T lamJ
    have hmaps : (lamJ : _ →+* T).comp (algebraMap B (Localization.Away (g j))) =
        (lamI : _ →+* T).comp (algebraMap B (Localization.Away (g i))) := by
      refine RingHom.ext fun b => ?_
      show μ (IsLocalization.Away.awayToAwayLeft (g j) (g i) (algebraMap B _ b)) =
        μ (IsLocalization.Away.awayToAwayRight (g i) (g j) (algebraMap B _ b))
      rw [IsLocalization.Away.awayToAwayLeft_eq, IsLocalization.Away.awayToAwayRight_eq]
    have key := transfer i T lamI ((Y j).map (lamJ : _ →+* T)) ((ρ j).map (lamJ : _ →+* T)) hJ1 (by rw [hJ2, hmaps])
    exact key.symm.trans (hspec' j T lamJ)
  have hcompat : ∀ i j : Fin r,
      IsLocalization.Away.awayToAwayRight (S := Localization.Away (g i)) (g i) (g j)
          (P := Localization.Away (g i * g j)) (e i) =
        IsLocalization.Away.awayToAwayLeft (S := Localization.Away (g j)) (g j) (g i)
          (P := Localization.Away (g i * g j)) (e j) := fun i j =>
    idem_eq_of_forall_iff _ _ ((he i).map (IsLocalization.Away.awayToAwayRight (g i) (g j)))
      ((he j).map (IsLocalization.Away.awayToAwayLeft (g j) (g i))) (hsame i j)

  obtain ⟨E, hEe, hEuniq⟩ := Localization.Away.existsUnique_forall_algebraMap_eq_of_span_eq_top g hg e hcompat
  have hEidem : IsIdempotentElem E :=
    hEuniq (E * E) fun i => by rw [map_mul, hEe i]; exact (he i).eq
  refine ⟨E, hEidem, fun B' _ _ φ => ⟨fun hS => ?_, fun hφ => ?_⟩⟩
  ·
    by_contra hne
    have hε : IsIdempotentElem (φ E) := hEidem.map φ
    have hJ : Ideal.span {φ E} ≠ ⊤ := by
      intro htop
      rw [Ideal.span_singleton_eq_top] at htop
      exact hne (htop.mul_left_cancel (hε.eq.trans (mul_one _).symm))
    obtain ⟨𝔪, h𝔪, hJ𝔪⟩ := Ideal.exists_le_maximal _ hJ
    have hField : IsField (B' ⧸ 𝔪) := (Ideal.Quotient.maximal_ideal_iff_isField_quotient 𝔪).mp h𝔪
    haveI : IsNoetherianRing (B' ⧸ 𝔪) := isNoetherianRing_of_isField hField
    haveI : Nontrivial (B' ⧸ 𝔪) :=
      ⟨⟨0, 1, fun h01 => h𝔪.ne_top (Ideal.Quotient.zero_eq_one_iff.mp h01)⟩⟩
    let ψ' : B' →ₐ[K₀] B' ⧸ 𝔪 := Ideal.Quotient.mkₐ K₀ 𝔪
    have hψε : ψ' (φ E) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (hJ𝔪 (Ideal.subset_span rfl))
    let θ : B →ₐ[K₀] B' ⧸ 𝔪 := ψ'.comp φ
    have hex : ∃ c, θ (g c) ≠ 0 := by
      by_contra hall
      push_neg at hall
      have h0 : Ideal.map (θ : B →+* B' ⧸ 𝔪) (Ideal.span (Set.range g)) = ⊥ := by
        rw [Ideal.map_span, Ideal.span_eq_bot]
        rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩
        exact hall c
      rw [hg, Ideal.map_top] at h0
      exact top_ne_bot h0
    obtain ⟨c, hc⟩ := hex
    have hu : IsUnit (θ (g c)) := by
      obtain ⟨b, hb⟩ := hField.mul_inv_cancel hc
      exact isUnit_iff_exists_inv.mpr ⟨b, hb⟩
    let lam' : Localization.Away (g c) →ₐ[K₀] B' ⧸ 𝔪 := liftAlg (g c) θ hu
    obtain ⟨h1, h2⟩ := present c (B' ⧸ 𝔪) lam'
    have hsp2 : Ideal.span (Set.range ((ρ c).map (lam' : _ →+* B' ⧸ 𝔪))) =
        (I.1.map (MvPowerSeries.map (φ : B →+* B'))).map (MvPowerSeries.map (ψ' : B' →+* B' ⧸ 𝔪)) := by
      rw [h2, Ideal.map_map, ← MvPowerSeries.map_comp]
      congr 2
      exact RingHom.ext fun b => liftAlg_algebraMap (g c) θ hu b
    have hS' := hS (B' ⧸ 𝔪) ψ'
    have hspκ : ((Y c).map (lam' : _ →+* B' ⧸ 𝔪)).IsSpecial (structureMap ι (ψof (B' ⧸ 𝔪))) := by
      refine hS' _ _ h1 ?_
      convert hsp2 using 2
    have h3 := (hspec' c (B' ⧸ 𝔪) lam').mp hspκ
    rw [← hEe c] at h3
    have h4 : θ E = 1 := (liftAlg_algebraMap (g c) θ hu E).symm.trans h3
    exact one_ne_zero (h4.symm.trans hψε)
  ·
    intro B'' _ _ _ ψ Y'' ρ'' hOD hsp
    have hpB'' : IsNilpotent (p : B'') := ⟨1, by rw [pow_one]; exact natCast_p_eq_zero (k := k) B''⟩
    let θ : B →ₐ[K₀] B'' := ψ.comp φ
    have hcov : Ideal.span (Set.range fun c => θ (g c)) = ⊤ := by
      have h0 := congrArg (Ideal.map (θ : B →+* B'')) hg
      rw [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at h0
      exact h0
    refine CerednikDrinfeld.FormalODModule.isSpecial_of_forall_isSpecial_map_away hpB'' _ Y'' (fun c => θ (g c)) hcov ?_
    intro c
    have hu : IsUnit (((IsScalarTower.toAlgHom K₀ B'' (Localization.Away (θ (g c)))).comp θ) (g c)) :=
      IsLocalization.Away.algebraMap_isUnit (θ (g c))
    have key := transfer c (Localization.Away (θ (g c)))
      (liftAlg (g c) ((IsScalarTower.toAlgHom K₀ B'' (Localization.Away (θ (g c)))).comp θ) hu)
      (Y''.map (algebraMap B'' _)) (ρ''.map (algebraMap B'' _)) ?_ ?_
    · have hj : (algebraMap B'' (Localization.Away (θ (g c)))).comp ((ψof B'').comp ι) =
          (ψof (Localization.Away (θ (g c)))).comp ι := by
        rw [← RingHom.comp_assoc]
        rfl
      rw [hj]
      refine key.mpr ?_
      rw [← hEe c]
      refine (liftAlg_algebraMap (g c) _ hu E).trans ?_
      show algebraMap B'' _ (ψ (φ E)) = 1
      rw [hφ, map_one, map_one]
    · have h := hOD.map (algebraMap B'' (Localization.Away (θ (g c))))
      rwa [FormalODModule.map_map, ← IsScalarTower.algebraMap_eq K₀ B''] at h
    · rw [span_range_map_eq_map, hsp, Ideal.map_map, Ideal.map_map, ← MvPowerSeries.map_comp, ← MvPowerSeries.map_comp]
      congr 2
      exact RingHom.ext fun b => (liftAlg_algebraMap (g c) _ hu b).symm

theorem specialAt_of_presentation {Φ : FormalODModule p K₀} (ι : Zp2 p →+* WittVector p k)
    {L : Type} [CommRing L] [IsNoetherianRing L] [Algebra K₀ L] (I : Ideal (MvPowerSeries (Fin 2) L))
    (Y : FormalODModule p L) (ρ : Series L) (hρ : FormalODModule.IsODHom (Φ.map (algebraMap K₀ L)) Y ρ)
    {d : ℕ} (hker : FormalODModule.HasKernelOfDegree ρ d)
    (hI : Ideal.span (Set.range ρ) = I) (hY : Y.IsSpecial ((ψof L).comp ι)) : SpecialAt Φ ι L I := by
  intro B'' _ _ _ ψ Y'' ρ'' hOD hsp
  have h1 : FormalODModule.IsODHom (Φ.map (algebraMap K₀ B'')) (Y.map (ψ : L →+* B'')) (ρ.map (ψ : L →+* B'')) := by
    have h := hρ.map (ψ : L →+* B'')
    rwa [FormalODModule.map_map, ψ.comp_algebraMap] at h
  have h2 : Ideal.span (Set.range (ρ.map (ψ : L →+* B''))) = I.map (MvPowerSeries.map (ψ : L →+* B'')) := by
    rw [span_range_map_eq_map, hI]
  have hker' : FormalODModule.HasKernelOfDegree (ρ.map (ψ : L →+* B'')) d :=
    CerednikDrinfeld.FormalODModule.hasKernelOfDegree_map (ψ : L →+* B'') ρ hρ.constantCoeff hker
  obtain ⟨u, v, hu, hv, hvu, huv, -, -⟩ :=
    CerednikDrinfeld.FormalODModule.exists_isODHom_comp_eq_of_span_range_eq_of_hasKernelOfDegree p
      (Φ.map (algebraMap K₀ B'')) (Y.map (ψ : L →+* B'')) Y'' (ρ.map (ψ : L →+* B'')) ρ'' h1 hOD hker' (h2.trans hsp.symm)
  have hYm : (Y.map (ψ : L →+* B'')).IsSpecial ((ψof B'').comp ι) := by
    have h := CerednikDrinfeld.FormalODModule.IsSpecial.map ((ψof L).comp ι) (ψ : L →+* B'') Y hY
    rwa [← RingHom.comp_assoc, algHom_comp_ψof ψ] at h
  exact CerednikDrinfeld.FormalODModule.IsSpecial.of_isODHom_of_comp_eq_id _ _ Y'' u v hu hv hvu huv hYm

end Witness

theorem special_locus {Φ : FormalODModule p K₀} (hΦ4 : Φ.HasHeight 4) (ι : Zp2 p →+* WittVector p k) (n m : ℕ)
    {H : Scheme.{0}} {q : H ⟶ Spec (CommRingCat.of K₀)} (hq : LocallyOfFiniteType q)
    (pt : ∀ (S : Type) [CommRing S] [Algebra K₀ S],
      {I : Ideal (MvPowerSeries (Fin 2) S) // PZ K₀ Φ (n + m) (4 * n) S I} ≃
        {g : Spec (CommRingCat.of S) ⟶ H // g ≫ q = Spec.map (CommRingCat.ofHom (algebraMap K₀ S))})
    (hmap : ∀ (S S' : Type) [CommRing S] [CommRing S'] [Algebra K₀ S] [Algebra K₀ S'] (φ : S →ₐ[K₀] S')
      (I : {I : Ideal (MvPowerSeries (Fin 2) S) // PZ K₀ Φ (n + m) (4 * n) S I}),
      PZ K₀ Φ (n + m) (4 * n) S' (I.1.map (MvPowerSeries.map (φ : S →+* S'))))
    (hnat : ∀ (S S' : Type) [CommRing S] [CommRing S'] [Algebra K₀ S] [Algebra K₀ S'] (φ : S →ₐ[K₀] S')
      (I : {I : Ideal (MvPowerSeries (Fin 2) S) // PZ K₀ Φ (n + m) (4 * n) S I}),
      (pt S' ⟨I.1.map (MvPowerSeries.map (φ : S →+* S')), hmap S S' φ I⟩).1 =
        Spec.map (CommRingCat.ofHom (φ : S →+* S')) ≫ (pt S I).1) :
    ∃ (X : Scheme.{0}) (ιX : X ⟶ H), IsOpenImmersion ιX ∧ IsClosedImmersion ιX ∧
      ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra K₀ B]
        (I : {I : Ideal (MvPowerSeries (Fin 2) B) // PZ K₀ Φ (n + m) (4 * n) B I}),
        SpecialAt Φ ι B I.1 ↔ ∃ g : Spec (CommRingCat.of B) ⟶ X, g ≫ ιX = (pt B I).1 := by

  haveI : IsNoetherianRing K₀ := inferInstance
  obtain ⟨X, ιX, hopen, hclosed, hiff⟩ :=
    AlgebraicGeometry.Scheme.exists_isOpenImmersion_isClosedImmersion_iff_of_isIdempotentElem_of_forall_exists_idempotent_of_finiteType
      K₀ (fun B _ _ => {I : Ideal (MvPowerSeries (Fin 2) B) // PZ K₀ Φ (n + m) (4 * n) B I})
      (fun B B' _ _ _ _ φ I => ⟨I.1.map (MvPowerSeries.map (φ : B →+* B')), hmap B B' φ I⟩)
      H q hq pt (fun B B' _ _ _ _ φ I => hnat B B' φ I) (fun B _ _ I => SpecialAt Φ ι B I.1)
      (fun B _ _ _ I => by
        haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing K₀ B
        exact exists_idempotent_specialAt_iff hΦ4 ι n m hmap B I)
  refine ⟨X, ιX, hopen, hclosed, fun B _ _ _ I => ?_⟩
  obtain ⟨e, he, hfun⟩ := exists_idempotent_specialAt_iff hΦ4 ι n m hmap B I
  exact hiff B I e he hfun

end D4

namespace D4

theorem map_congr {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] (M : ModuliPackage.{0, 0} p O) {B B' : Type} [CommRing B] [CommRing B']
    {ψ : O →+* B} {ψ' : O →+* B'} (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B'))
    (f f' : B →+* B') (hf : f.comp ψ = ψ') (hf' : f'.comp ψ = ψ') (hff : f = f') (x : M.obj B ψ hB) :
    M.map hB hB' f hf x = M.map hB hB' f' hf' x := by
  subst hff; rfl
end D4

namespace D4

open MvPowerSeries

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p]

local notation "K₀" => (WittVector p k ⧸ pIdeal p (WittVector p k))

theorem glue_opens' {X Y : Scheme} {J : Type} (U : J → X.Opens) (hU : ⨆ j, U j = ⊤)
    (g : ∀ j, (U j : Scheme) ⟶ Y)
    (hg : ∀ i j, ∃ (W : X.Opens) (hWi : W ≤ U i) (hWj : W ≤ U j), W = U i ⊓ U j ∧
      X.homOfLE hWi ≫ g i = X.homOfLE hWj ≫ g j) :
    ∃ φ : X ⟶ Y, ∀ j, (U j).ι ≫ φ = g j := by
  apply glue_opens U hU g
  intro i j
  obtain ⟨W, hWi, hWj, hW, h⟩ := hg i j
  subst hW
  exact h

noncomputable abbrev ψvia (S L : Type) [CommRing S] [Algebra K₀ S] [CommRing L] [Algebra S L] : WittVector p k →+* L :=
  (algebraMap S L).comp (ψof S)

theorem ψvia_eq (S L : Type) [CommRing S] [Algebra K₀ S] [CommRing L] [Algebra S L] [Algebra K₀ L] [IsScalarTower K₀ S L] :
    ψvia (p := p) (k := k) S L = ψof L := by
  show ((algebraMap S L).comp (algebraMap K₀ S)).comp _ = (algebraMap K₀ L).comp _
  rw [← IsScalarTower.algebraMap_eq]

theorem isNilpotent_p (L : Type) [CommRing L] [Algebra K₀ L] : IsNilpotent (p : L) :=
  ⟨1, by rw [pow_one]; exact natCast_p_eq_zero (k := k) L⟩

theorem exists_point_of_cover {Φ : FormalODModule p K₀} (hΦ4 : Φ.HasHeight 4) (ι : Zp2 p →+* WittVector p k) (n m : ℕ)
    {H : Scheme.{0}} {q : H ⟶ Spec (CommRingCat.of K₀)}
    (pt : ∀ (S : Type) [CommRing S] [Algebra K₀ S],
      {I : Ideal (MvPowerSeries (Fin 2) S) // PZ K₀ Φ (n + m) (4 * n) S I} ≃
        {g : Spec (CommRingCat.of S) ⟶ H // g ≫ q = Spec.map (CommRingCat.ofHom (algebraMap K₀ S))})
    (hmap : ∀ (S S' : Type) [CommRing S] [CommRing S'] [Algebra K₀ S] [Algebra K₀ S'] (φ : S →ₐ[K₀] S')
      (I : {I : Ideal (MvPowerSeries (Fin 2) S) // PZ K₀ Φ (n + m) (4 * n) S I}),
      PZ K₀ Φ (n + m) (4 * n) S' (I.1.map (MvPowerSeries.map (φ : S →+* S'))))
    (hnat : ∀ (S S' : Type) [CommRing S] [CommRing S'] [Algebra K₀ S] [Algebra K₀ S'] (φ : S →ₐ[K₀] S')
      (I : {I : Ideal (MvPowerSeries (Fin 2) S) // PZ K₀ Φ (n + m) (4 * n) S I}),
      (pt S' ⟨I.1.map (MvPowerSeries.map (φ : S →+* S')), hmap S S' φ I⟩).1 =
        Spec.map (CommRingCat.ofHom (φ : S →+* S')) ≫ (pt S I).1)
    (M : ModuliPackage.{0, 0} p (WittVector p k))
    (η : ∀ (B : Type) [CommRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)), Rigidified p Φ B → M.obj B ψ hB)
    (hη1 : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B))
      (t t' : Rigidified p Φ B), t.IsAdmissible ι ψ → t'.IsAdmissible ι ψ → (η B ψ hB t = η B ψ hB t' ↔ t.IsIsomorphic t'))
    (hη2 : ∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] (ψ : WittVector p k →+* B)
      (ψ' : WittVector p k →+* B') (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (f : B →+* B')
      (hf : f.comp ψ = ψ') (t : Rigidified p Φ B), t.IsAdmissible ι ψ → η B' ψ' hB' (t.map f) = M.map hB hB' f hf (η B ψ hB t))
    (S : Type) [CommRing S] [IsNoetherianRing S] [Algebra K₀ S] (hS : IsNilpotent (p : S)) (x : M.obj S (ψof S) hS)
    {r : ℕ} (f : Fin r → S) (hspan : Ideal.span (Set.range f) = ⊤)
    (hL : ∀ i, IsNilpotent (p : Localization.Away (f i)))
    (t : ∀ i, Rigidified p Φ (Localization.Away (f i)))
    (ht : ∀ i, (t i).IsAdmissible ι (ψvia S (Localization.Away (f i))))
    (hn : ∀ i, (t i).n = n)
    (hcont : ∀ i j, ((t i).Φbar (ψvia S (Localization.Away (f i)))).act ((p : Zp2 p) ^ (n + m)) j ∈ Ideal.span (Set.range (t i).ρ))
    (hηt : ∀ i, η _ (ψvia S (Localization.Away (f i))) (hL i) (t i) = M.map hS (hL i) (algebraMap S _) rfl x) :
    ∃ φ : Spec (CommRingCat.of S) ⟶ H, φ ≫ q = Spec.map (CommRingCat.ofHom (algebraMap K₀ S)) ∧
      ∀ i, ∃ (ht' : (t i).IsAdmissible ι (ψof (Localization.Away (f i))))
        (hcont' : ∀ j, ((t i).Φbar (ψof (Localization.Away (f i)))).act ((p : Zp2 p) ^ (n + m)) j ∈ Ideal.span (Set.range (t i).ρ)),
        Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (f i)))) ≫ φ =
          (pointOfTriple hΦ4 ι n m pt hmap (t i) ht' (hn i) hcont').1 := by
  classical

  have ht' : ∀ i, (t i).IsAdmissible ι (ψof (Localization.Away (f i))) := fun i => by
    rw [← ψvia_eq S]; exact ht i
  have hcont' : ∀ i j, ((t i).Φbar (ψof (Localization.Away (f i)))).act ((p : Zp2 p) ^ (n + m)) j ∈
      Ideal.span (Set.range (t i).ρ) := fun i => by rw [← ψvia_eq S]; exact hcont i
  let Pt : ∀ i, {g : Spec (CommRingCat.of (Localization.Away (f i))) ⟶ H //
      g ≫ q = Spec.map (CommRingCat.ofHom (algebraMap K₀ (Localization.Away (f i))))} :=
    fun i => pointOfTriple hΦ4 ι n m pt hmap (t i) (ht' i) (hn i) (hcont' i)
  let U : Fin r → (Spec (CommRingCat.of S)).Opens := fun i => PrimeSpectrum.basicOpen (f i)
  let eU : ∀ i, (U i : Scheme) ≅ Spec (CommRingCat.of (Localization.Away (f i))) :=
    fun i => basicOpenIsoSpecAway (R := CommRingCat.of S) (f i)
  have heU : ∀ i, (eU i).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (f i)))) = (U i).ι :=
    fun i => IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  let g : ∀ i, (U i : Scheme) ⟶ H := fun i => (eU i).hom ≫ (Pt i).1

  have hLoc : ∀ i, IsNoetherianRing (Localization.Away (f i)) := fun i =>
    IsLocalization.isNoetherianRing (Submonoid.powers (f i)) _ inferInstance
  haveI hjiAll : ∀ i j, IsLocalization.Away (f j * f i) (Localization.Away (f i * f j)) := fun i j => by
    rw [mul_comm]; infer_instance
  have main : ∀ i j, Spec.map (CommRingCat.ofHom (IsLocalization.Away.awayToAwayRight (f i) (f j)
        (P := Localization.Away (f i * f j)))) ≫ (Pt i).1 =
      Spec.map (CommRingCat.ofHom (IsLocalization.Away.awayToAwayRight (f j) (f i)
        (P := Localization.Away (f i * f j)))) ≫ (Pt j).1 := by
    intro i j
    let Lij := Localization.Away (f i * f j)
    haveI : IsNoetherianRing Lij := IsLocalization.isNoetherianRing (Submonoid.powers (f i * f j)) _ inferInstance
    have hLij : IsNilpotent (p : Lij) := isNilpotent_p (k := k) Lij
    let ai : Localization.Away (f i) →ₐ[K₀] Lij := awayRightAlg (f i) (f j) Lij
    let aj : Localization.Away (f j) →ₐ[K₀] Lij := awayRightAlg (f j) (f i) Lij

    have hai : (ai : Localization.Away (f i) →+* Lij).comp (ψvia S (Localization.Away (f i))) = ψvia (p := p) (k := k) S Lij := by
      show ((ai : Localization.Away (f i) →+* Lij).comp (algebraMap S _)).comp (ψof (p := p) (k := k) S) = (algebraMap S Lij).comp (ψof (p := p) (k := k) S)
      rw [awayRightAlg_comp_algebraMap]
    have haj : (aj : Localization.Away (f j) →+* Lij).comp (ψvia S (Localization.Away (f j))) = ψvia (p := p) (k := k) S Lij := by
      show ((aj : Localization.Away (f j) →+* Lij).comp (algebraMap S _)).comp (ψof (p := p) (k := k) S) = (algebraMap S Lij).comp (ψof (p := p) (k := k) S)
      rw [awayRightAlg_comp_algebraMap]
    have hadm_i : ((t i).map (ai : _ →+* Lij)).IsAdmissible ι (ψvia S Lij) := by
      rw [← hai]; exact Rigidified.IsAdmissible.map_ringHom ι _ _ (t i) (ht i)
    have hadm_j : ((t j).map (aj : _ →+* Lij)).IsAdmissible ι (ψvia S Lij) := by
      rw [← haj]; exact Rigidified.IsAdmissible.map_ringHom ι _ _ (t j) (ht j)

    have hηi : η Lij (ψvia S Lij) hLij ((t i).map (ai : _ →+* Lij)) = M.map hS hLij (algebraMap S Lij) rfl x := by
      rw [hη2 _ _ (ψvia S (Localization.Away (f i))) (ψvia S Lij) (hL i) hLij (ai : _ →+* Lij) hai (t i) (ht i), hηt i,
        ← M.map_comp]
      exact map_congr M hS hLij _ _ _ _ (awayRightAlg_comp_algebraMap (p := p) (k := k) (f i) (f j) Lij) x
    have hηj : η Lij (ψvia S Lij) hLij ((t j).map (aj : _ →+* Lij)) = M.map hS hLij (algebraMap S Lij) rfl x := by
      rw [hη2 _ _ (ψvia S (Localization.Away (f j))) (ψvia S Lij) (hL j) hLij (aj : _ →+* Lij) haj (t j) (ht j), hηt j,
        ← M.map_comp]
      exact map_congr M hS hLij _ _ _ _ (awayRightAlg_comp_algebraMap (p := p) (k := k) (f j) (f i) Lij) x
    have hiso : ((t i).map (ai : _ →+* Lij)).IsIsomorphic ((t j).map (aj : _ →+* Lij)) :=
      (hη1 Lij (ψvia S Lij) hLij _ _ hadm_i hadm_j).mp (hηi.trans hηj.symm)

    have ei := pointOfTriple_map hΦ4 ι n m pt hmap hnat ai (t i) (ht' i) (hn i) (hcont' i)
      (isAdmissible_map_alg ι ai (t i) (ht' i)) (hn i) (hcont_map_alg ai (t i) (n + m) (hcont' i))
    have ej := pointOfTriple_map hΦ4 ι n m pt hmap hnat aj (t j) (ht' j) (hn j) (hcont' j)
      (isAdmissible_map_alg ι aj (t j) (ht' j)) (hn j) (hcont_map_alg aj (t j) (n + m) (hcont' j))
    show Spec.map (CommRingCat.ofHom (ai : Localization.Away (f i) →+* Lij)) ≫ (Pt i).1 =
      Spec.map (CommRingCat.ofHom (aj : Localization.Away (f j) →+* Lij)) ≫ (Pt j).1
    rw [← ei, ← ej]
    exact pointOfTriple_congr hΦ4 ι n m pt hmap _ _ _ _ _ _ _ _ hiso

  have hcompat : ∀ i j, ∃ (W : (Spec (CommRingCat.of S)).Opens) (hWi : W ≤ U i) (hWj : W ≤ U j), W = U i ⊓ U j ∧
      (Spec (CommRingCat.of S)).homOfLE hWi ≫ g i = (Spec (CommRingCat.of S)).homOfLE hWj ≫ g j := by
    intro i j
    have hW : (PrimeSpectrum.basicOpen (f i * f j) : (Spec (CommRingCat.of S)).Opens) = U i ⊓ U j :=
      PrimeSpectrum.basicOpen_mul (f i) (f j)
    refine ⟨PrimeSpectrum.basicOpen (f i * f j), hW.le.trans inf_le_left, hW.le.trans inf_le_right, hW, ?_⟩
    have hi := basicOpenIsoSpecAway_inv_homOfLE (R := CommRingCat.of S) (f i) (f j) (f i * f j) rfl
    have hj := basicOpenIsoSpecAway_inv_homOfLE (R := CommRingCat.of S) (f j) (f i) (f i * f j) (mul_comm _ _)
    rw [← cancel_epi (basicOpenIsoSpecAway (R := CommRingCat.of S) (f i * f j)).inv]
    simp only [g]
    rw [← Category.assoc, hi, ← Category.assoc ((basicOpenIsoSpecAway (R := CommRingCat.of S) (f i * f j)).inv), hj]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, eU]
    exact main i j

  obtain ⟨φ, hφ⟩ := glue_opens' U (iSup_basicOpen_eq_top f hspan) g hcompat
  have hres : ∀ i, Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (f i)))) ≫ φ = (Pt i).1 := by
    intro i
    rw [← cancel_epi (eU i).hom, ← Category.assoc, heU i, hφ i]
  refine ⟨φ, ?_, fun i => ⟨ht' i, hcont' i, hres i⟩⟩

  apply glue_opens_unique U (iSup_basicOpen_eq_top f hspan)
  intro i
  rw [← heU i, Category.assoc, Category.assoc]
  congr 1
  rw [← Category.assoc, hres i, (Pt i).2, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

end D4

namespace D4

open MvPowerSeries

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p]

local notation "K₀" => (WittVector p k ⧸ pIdeal p (WittVector p k))

def Compat {Φ : FormalODModule p K₀} (hΦ4 : Φ.HasHeight 4) (ι : Zp2 p →+* WittVector p k) (n m : ℕ)
    {H : Scheme.{0}} {q : H ⟶ Spec (CommRingCat.of K₀)}
    (pt : ∀ (S : Type) [CommRing S] [Algebra K₀ S],
      {I : Ideal (MvPowerSeries (Fin 2) S) // PZ K₀ Φ (n + m) (4 * n) S I} ≃
        {g : Spec (CommRingCat.of S) ⟶ H // g ≫ q = Spec.map (CommRingCat.ofHom (algebraMap K₀ S))})
    (hmap : ∀ (S S' : Type) [CommRing S] [CommRing S'] [Algebra K₀ S] [Algebra K₀ S'] (φ : S →ₐ[K₀] S')
      (I : {I : Ideal (MvPowerSeries (Fin 2) S) // PZ K₀ Φ (n + m) (4 * n) S I}),
      PZ K₀ Φ (n + m) (4 * n) S' (I.1.map (MvPowerSeries.map (φ : S →+* S'))))
    (M : ModuliPackage.{0, 0} p (WittVector p k))
    (η : ∀ (B : Type) [CommRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)), Rigidified p Φ B → M.obj B ψ hB)
    (S : Type) [CommRing S] [IsNoetherianRing S] [Algebra K₀ S] (hS : IsNilpotent (p : S))
    (φ : Spec (CommRingCat.of S) ⟶ H) (x : M.obj S (ψof S) hS) : Prop :=
  ∀ (g : S) (t : Rigidified p Φ (Localization.Away g))
    (ht : t.IsAdmissible ι (ψof (Localization.Away g))) (hn : t.n = n)
    (hcont : ∀ j, (t.Φbar (ψof (Localization.Away g))).act ((p : Zp2 p) ^ (n + m)) j ∈ Ideal.span (Set.range t.ρ)),
    haveI : IsNoetherianRing (Localization.Away g) := IsLocalization.isNoetherianRing (Submonoid.powers g) _ inferInstance
    η _ (ψvia S (Localization.Away g)) (isNilpotent_p (k := k) _) t =
        M.map hS (isNilpotent_p (k := k) _) (algebraMap S (Localization.Away g)) rfl x →
      Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g))) ≫ φ =
        (pointOfTriple hΦ4 ι n m pt hmap t ht hn hcont).1

end D4

namespace D4

open MvPowerSeries

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p]

local notation "K₀" => (WittVector p k ⧸ pIdeal p (WittVector p k))

abbrev Pnm {Φ : FormalODModule p K₀} (ι : Zp2 p →+* WittVector p k)
    (M : ModuliPackage.{0, 0} p (WittVector p k))
    (η : ∀ (B : Type) [CommRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)), Rigidified p Φ B → M.obj B ψ hB)
    (n m : ℕ) (S : Type) [CommRing S] [IsNoetherianRing S] [Algebra K₀ S] (hS : IsNilpotent (p : S))
    (x : M.obj S ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) S).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) hS) : Prop :=
  ∃ (r : ℕ) (f : Fin r → S), Ideal.span (Set.range f) = ⊤ ∧
            ∀ (i : Fin r) (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra S L] [IsLocalization.Away (f i) L]
              (hL : IsNilpotent (p : L)),
              ∃ t : Rigidified p Φ L, t.IsAdmissible ι ((algebraMap S L).comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) S).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) ∧ t.n = n ∧
                (∀ j : Fin 2, (t.Φbar ((algebraMap S L).comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) S).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))))).act ((p : Zp2 p) ^ (n + m)) j ∈ Ideal.span (Set.range t.ρ)) ∧
                η L ((algebraMap S L).comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) S).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) hL t =
                  M.map (ψ' := (algebraMap S L).comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) S).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) hS hL (algebraMap S L) rfl x

theorem Compat.unique_point {Φ : FormalODModule p K₀} (hΦ4 : Φ.HasHeight 4) (ι : Zp2 p →+* WittVector p k) (n m : ℕ)
    {H : Scheme.{0}} {q : H ⟶ Spec (CommRingCat.of K₀)}
    (pt : ∀ (S : Type) [CommRing S] [Algebra K₀ S],
      {I : Ideal (MvPowerSeries (Fin 2) S) // PZ K₀ Φ (n + m) (4 * n) S I} ≃
        {g : Spec (CommRingCat.of S) ⟶ H // g ≫ q = Spec.map (CommRingCat.ofHom (algebraMap K₀ S))})
    (hmap : ∀ (S S' : Type) [CommRing S] [CommRing S'] [Algebra K₀ S] [Algebra K₀ S'] (φ : S →ₐ[K₀] S')
      (I : {I : Ideal (MvPowerSeries (Fin 2) S) // PZ K₀ Φ (n + m) (4 * n) S I}),
      PZ K₀ Φ (n + m) (4 * n) S' (I.1.map (MvPowerSeries.map (φ : S →+* S'))))
    (M : ModuliPackage.{0, 0} p (WittVector p k))
    (η : ∀ (B : Type) [CommRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)), Rigidified p Φ B → M.obj B ψ hB)
    (S : Type) [CommRing S] [IsNoetherianRing S] [Algebra K₀ S] (hS : IsNilpotent (p : S))
    (φ φ' : Spec (CommRingCat.of S) ⟶ H) (x : M.obj S (ψof S) hS)
    (hφ : Compat hΦ4 ι n m pt hmap M η S hS φ x) (hφ' : Compat hΦ4 ι n m pt hmap M η S hS φ' x)
    (hx : Pnm ι M η n m S hS x) : φ = φ' := by
  obtain ⟨r, f, hspan, hloc⟩ := hx
  apply glue_opens_unique (fun i => (PrimeSpectrum.basicOpen (f i) : (Spec (CommRingCat.of S)).Opens))
    (iSup_basicOpen_eq_top f hspan)
  intro i
  haveI : IsNoetherianRing (Localization.Away (f i)) := IsLocalization.isNoetherianRing (Submonoid.powers (f i)) _ inferInstance
  obtain ⟨t, ht, hn, hcont, hηt⟩ := hloc i (Localization.Away (f i)) (isNilpotent_p (k := k) _)
  have ht' : t.IsAdmissible ι (ψof (Localization.Away (f i))) := by rw [← ψvia_eq S]; exact ht
  have hcont' : ∀ j, (t.Φbar (ψof (Localization.Away (f i)))).act ((p : Zp2 p) ^ (n + m)) j ∈ Ideal.span (Set.range t.ρ) := by
    rw [← ψvia_eq S]; exact hcont
  have e1 := hφ (f i) t ht' hn hcont' hηt
  have e2 := hφ' (f i) t ht' hn hcont' hηt
  have hfac := IsOpenImmersion.isoOfRangeEq_hom_fac (Scheme.Opens.ι (X := Spec (CommRingCat.of S)) (PrimeSpectrum.basicOpen (f i)))
    (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (f i)))))
    (by simp only [Scheme.Opens.range_ι]; exact (PrimeSpectrum.localization_away_comap_range _ _).symm)

  rw [← hfac, Category.assoc, Category.assoc, e1, e2]

end D4

namespace D4

open MvPowerSeries

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p]

local notation "K₀" => (WittVector p k ⧸ pIdeal p (WittVector p k))

namespace J7

noncomputable def algOf (S L : Type) [CommRing S] [Algebra K₀ S] [CommRing L] [Algebra S L] [Algebra K₀ L]
    [IsScalarTower K₀ S L] : S →ₐ[K₀] L :=
  { toRingHom := algebraMap S L
    commutes' := fun r => (IsScalarTower.algebraMap_apply K₀ S L r).symm }

theorem algOf_coe (S L : Type) [CommRing S] [Algebra K₀ S] [CommRing L] [Algebra S L] [Algebra K₀ L]
    [IsScalarTower K₀ S L] : (algOf (p := p) (k := k) S L : S →+* L) = algebraMap S L := rfl

noncomputable def liftAlg {S : Type} [CommRing S] [Algebra K₀ S] (g : S) (P : Type) [CommRing P] [Algebra S P]
    [Algebra K₀ P] [IsScalarTower K₀ S P] (hg : IsUnit (algebraMap S P g)) : Localization.Away g →ₐ[K₀] P :=
  { toRingHom := IsLocalization.Away.lift g hg
    commutes' := fun r => by
      show IsLocalization.Away.lift g hg (algebraMap K₀ (Localization.Away g) r) = algebraMap K₀ P r
      rw [IsScalarTower.algebraMap_apply K₀ S (Localization.Away g) r, IsLocalization.Away.lift_eq,
        ← IsScalarTower.algebraMap_apply K₀ S P r] }

theorem liftAlg_coe {S : Type} [CommRing S] [Algebra K₀ S] (g : S) (P : Type) [CommRing P] [Algebra S P]
    [Algebra K₀ P] [IsScalarTower K₀ S P] (hg : IsUnit (algebraMap S P g)) :
    (liftAlg (p := p) (k := k) g P hg : Localization.Away g →+* P) = IsLocalization.Away.lift g hg := rfl

theorem liftAlg_comp_algebraMap {S : Type} [CommRing S] [Algebra K₀ S] (g : S) (P : Type) [CommRing P] [Algebra S P]
    [Algebra K₀ P] [IsScalarTower K₀ S P] (hg : IsUnit (algebraMap S P g)) :
    (liftAlg (p := p) (k := k) g P hg : Localization.Away g →+* P).comp (algebraMap S (Localization.Away g)) =
      algebraMap S P :=
  IsLocalization.Away.lift_comp g hg

theorem hasHeight_map {Φ : FormalODModule p K₀} (hΦ4 : Φ.HasHeight 4) {B' : Type} [CommRing B'] (f : K₀ →+* B') :
    (Φ.map f).HasHeight 4 := by
  show FormalODModule.HasKernelOfDegree ((Φ.map f).act (p : Zp2 p)) (p ^ 4)
  rw [FormalODModule.map_act]
  exact CerednikDrinfeld.FormalODModule.hasKernelOfDegree_map f _ (Φ.isLawHom_act _).1 hΦ4

theorem hcont_map_ringHom {Φ : FormalODModule p K₀} {B B' : Type} [CommRing B] [CommRing B'] (ψ : WittVector p k →+* B)
    (f : B →+* B') (t : Rigidified p Φ B) (e : ℕ)
    (hcont : ∀ j, (t.Φbar ψ).act ((p : Zp2 p) ^ e) j ∈ Ideal.span (Set.range t.ρ)) :
    ∀ j, ((t.map f).Φbar (f.comp ψ)).act ((p : Zp2 p) ^ e) j ∈ Ideal.span (Set.range (t.map f).ρ) := by
  intro j
  rw [Rigidified.Φbar_map, Rigidified.map_ρ, FormalODModule.map_act, span_range_map_eq_map]
  exact Ideal.mem_map_of_mem _ (hcont j)

noncomputable def tripleOf {Φ : FormalODModule p K₀} {B' : Type} [CommRing B'] (Y : FormalODModule p B') (n : ℕ)
    (ρ : Series B') : Rigidified p Φ B' :=
  ⟨Y, n, ρ.map (Ideal.Quotient.mk (pIdeal p B'))⟩

@[scoped simp] theorem tripleOf_n {Φ : FormalODModule p K₀} {B' : Type} [CommRing B'] (Y : FormalODModule p B') (n : ℕ)
    (ρ : Series B') : (tripleOf (Φ := Φ) Y n ρ).n = n := rfl

@[scoped simp] theorem tripleOf_X {Φ : FormalODModule p K₀} {B' : Type} [CommRing B'] (Y : FormalODModule p B') (n : ℕ)
    (ρ : Series B') : (tripleOf (Φ := Φ) Y n ρ).X = Y := rfl

@[scoped simp] theorem tripleOf_ρ {Φ : FormalODModule p K₀} {B' : Type} [CommRing B'] (Y : FormalODModule p B') (n : ℕ)
    (ρ : Series B') : (tripleOf (Φ := Φ) Y n ρ).ρ = ρ.map (Ideal.Quotient.mk (pIdeal p B')) := rfl

theorem map_algebraMap_quot {Φ : FormalODModule p K₀} (B' : Type) [CommRing B'] [Algebra K₀ B'] :
    Φ.map (algebraMap K₀ (B' ⧸ pIdeal p B')) = (Φ.map (algebraMap K₀ B')).map (Ideal.Quotient.mk (pIdeal p B')) := by
  rw [FormalODModule.map_map, Ideal.Quotient.mk_comp_algebraMap]

theorem tripleOf_isAdmissible {Φ : FormalODModule p K₀} (hΦ4 : Φ.HasHeight 4) (ι : Zp2 p →+* WittVector p k) {B' : Type}
    [CommRing B'] [IsNoetherianRing B'] [Algebra K₀ B'] (Y : FormalODModule p B') (n : ℕ) (ρ : Series B')
    (hY : FormalODModule.IsIsogenyOfHeight (Φ.map (algebraMap K₀ B')) Y ρ (4 * n))
    (hsp : Y.IsSpecial (structureMap ι (ψof B'))) :
    (tripleOf (Φ := Φ) Y n ρ).IsAdmissible ι (ψof B') := by
  refine ⟨hsp, ?_, ?_⟩
  · exact CerednikDrinfeld.FormalODModule.hasHeight_four_of_isIsogenyOfHeight p (isNilpotent_p (k := k) B')
      (Φ.map (algebraMap K₀ B')) Y ρ (4 * n) hY (hasHeight_map hΦ4 _)
  · show FormalODModule.IsIsogenyOfHeight (Φ.map (residueMap (ψof B'))) (Y.map (Ideal.Quotient.mk (pIdeal p B')))
      (ρ.map (Ideal.Quotient.mk (pIdeal p B'))) (4 * n)
    rw [← algebraMap_quot_eq_residueMap, map_algebraMap_quot]
    exact ⟨hY.1.map _, CerednikDrinfeld.FormalODModule.hasKernelOfDegree_map _ ρ hY.1.constantCoeff hY.2⟩

theorem tripleOf_hcont {Φ : FormalODModule p K₀} {B' : Type} [CommRing B'] [Algebra K₀ B'] (Y : FormalODModule p B')
    (n : ℕ) (ρ : Series B') (e : ℕ)
    (hc : ∀ j, (Φ.map (algebraMap K₀ B')).act ((p : Zp2 p) ^ e) j ∈ Ideal.span (Set.range ρ)) :
    ∀ j, ((tripleOf (Φ := Φ) Y n ρ).Φbar (ψof B')).act ((p : Zp2 p) ^ e) j ∈
      Ideal.span (Set.range (tripleOf (Φ := Φ) Y n ρ).ρ) := by
  intro j
  show (Φ.map (residueMap (ψof B'))).act ((p : Zp2 p) ^ e) j ∈
    Ideal.span (Set.range (ρ.map (Ideal.Quotient.mk (pIdeal p B'))))
  rw [← algebraMap_quot_eq_residueMap, map_algebraMap_quot, FormalODModule.map_act, span_range_map_eq_map]
  exact Ideal.mem_map_of_mem _ (hc j)

theorem kerIdeal_tripleOf {Φ : FormalODModule p K₀} {B' : Type} [CommRing B'] [Algebra K₀ B'] (Y : FormalODModule p B')
    (n : ℕ) (ρ : Series B') : kerIdeal (k := k) (tripleOf (Φ := Φ) Y n ρ) = Ideal.span (Set.range ρ) := by
  unfold kerIdeal
  rw [tripleOf_ρ, span_range_map_eq_map, Ideal.map_map, ← MvPowerSeries.map_comp]
  have hcomp : (quotAlgEquiv (k := k) B').symm.toRingEquiv.toRingHom.comp (Ideal.Quotient.mk (pIdeal p B')) =
      RingHom.id B' := by
    ext x
    exact quotAlgEquiv_symm_mk (k := k) B' x
  rw [hcomp, MvPowerSeries.map_id, Ideal.map_id]

theorem span_eq_kerIdeal_map {Φ : FormalODModule p K₀} {L : Type} [CommRing L] [Algebra K₀ L] (t : Rigidified p Φ L) :
    Ideal.span (Set.range t.ρ) =
      (kerIdeal (k := k) t).map (MvPowerSeries.map (quotAlgEquiv (k := k) L).toRingEquiv.toRingHom) := by
  unfold kerIdeal
  have hcomp : (quotAlgEquiv (p := p) (k := k) L).toRingEquiv.toRingHom.comp
      (quotAlgEquiv (p := p) (k := k) L).symm.toRingEquiv.toRingHom = RingHom.id (L ⧸ pIdeal p L) := by
    ext x
    exact (quotAlgEquiv (p := p) (k := k) L).apply_symm_apply x
  rw [Ideal.map_map, ← MvPowerSeries.map_comp, hcomp, MvPowerSeries.map_id, Ideal.map_id]

theorem isIsomorphic_of_kerIdeal_eq {Φ : FormalODModule p K₀} (ι : Zp2 p →+* WittVector p k) {L : Type} [CommRing L]
    [IsNoetherianRing L] [Algebra K₀ L] (t t' : Rigidified p Φ L)
    (ht : t.IsAdmissible ι (ψof L)) (ht' : t'.IsAdmissible ι (ψof L)) (hn : t.n = t'.n)
    (hI : kerIdeal (k := k) t = kerIdeal (k := k) t') : t.IsIsomorphic t' := by
  apply isIsomorphic_of_span_eq ι t t' ht ht' hn
  rw [span_eq_kerIdeal_map (k := k) t, span_eq_kerIdeal_map (k := k) t', hI]

theorem kerIdeal_tripleOf_map {Φ : FormalODModule p K₀} {B' B'' : Type} [CommRing B'] [Algebra K₀ B'] [CommRing B'']
    [Algebra K₀ B''] (a : B' →ₐ[K₀] B'') (Y : FormalODModule p B') (n : ℕ) (ρ : Series B')
    {S : Type} [CommRing S] (I : Ideal (MvPowerSeries (Fin 2) S)) (s : S →+* B')
    (hρ : Ideal.span (Set.range ρ) = I.map (MvPowerSeries.map s)) :
    kerIdeal (k := k) ((tripleOf (Φ := Φ) Y n ρ).map (a : B' →+* B'')) =
      I.map (MvPowerSeries.map ((a : B' →+* B'').comp s)) := by
  rw [kerIdeal_map, kerIdeal_tripleOf, hρ, Ideal.map_map, ← MvPowerSeries.map_comp]

end J7
p2m_reactivate "P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_scheme_nilpPoints_equiv_subtype_act_pow_mem_span_and_isClosedImmersion_toProjSpace.D4.J7"

end D4
p2m_reactivate "P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_scheme_nilpPoints_equiv_subtype_act_pow_mem_span_and_isClosedImmersion_toProjSpace.D4.J7 P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_scheme_nilpPoints_equiv_subtype_act_pow_mem_span_and_isClosedImmersion_toProjSpace.D4"

namespace D4

open MvPowerSeries

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p]

local notation "K₀" => (WittVector p k ⧸ pIdeal p (WittVector p k))

namespace J7

theorem pointOfTriple_eq {Φ : FormalODModule p K₀} (hΦ4 : Φ.HasHeight 4) (ι : Zp2 p →+* WittVector p k) (n m : ℕ)
    {H : Scheme.{0}} {q : H ⟶ Spec (CommRingCat.of K₀)}
    (pt : ∀ (S : Type) [CommRing S] [Algebra K₀ S],
      {I : Ideal (MvPowerSeries (Fin 2) S) // PZ K₀ Φ (n + m) (4 * n) S I} ≃
        {g : Spec (CommRingCat.of S) ⟶ H // g ≫ q = Spec.map (CommRingCat.ofHom (algebraMap K₀ S))})
    (hmap : ∀ (S S' : Type) [CommRing S] [CommRing S'] [Algebra K₀ S] [Algebra K₀ S'] (φ : S →ₐ[K₀] S')
      (I : {I : Ideal (MvPowerSeries (Fin 2) S) // PZ K₀ Φ (n + m) (4 * n) S I}),
      PZ K₀ Φ (n + m) (4 * n) S' (I.1.map (MvPowerSeries.map (φ : S →+* S'))))
    (hnat : ∀ (S S' : Type) [CommRing S] [CommRing S'] [Algebra K₀ S] [Algebra K₀ S'] (φ : S →ₐ[K₀] S')
      (I : {I : Ideal (MvPowerSeries (Fin 2) S) // PZ K₀ Φ (n + m) (4 * n) S I}),
      (pt S' ⟨I.1.map (MvPowerSeries.map (φ : S →+* S')), hmap S S' φ I⟩).1 =
        Spec.map (CommRingCat.ofHom (φ : S →+* S')) ≫ (pt S I).1)
    (S : Type) [CommRing S] [Algebra K₀ S]
    (φ : Spec (CommRingCat.of S) ⟶ H) (hφ : φ ≫ q = Spec.map (CommRingCat.ofHom (algebraMap K₀ S)))
    {B' : Type} [CommRing B'] [IsNoetherianRing B'] [Algebra K₀ B'] (a : S →ₐ[K₀] B')
    (t : Rigidified p Φ B') (ht : t.IsAdmissible ι (ψof B')) (hn : t.n = n)
    (hcont : ∀ j, (t.Φbar (ψof B')).act ((p : Zp2 p) ^ (n + m)) j ∈ Ideal.span (Set.range t.ρ))
    (hker : kerIdeal (k := k) t = ((pt S).symm ⟨φ, hφ⟩).1.map (MvPowerSeries.map (a : S →+* B'))) :
    (pointOfTriple hΦ4 ι n m pt hmap t ht hn hcont).1 = Spec.map (CommRingCat.ofHom (a : S →+* B')) ≫ φ := by
  have h1 := hnat S B' a ((pt S).symm ⟨φ, hφ⟩)
  simp only [Equiv.apply_symm_apply] at h1
  unfold pointOfTriple
  rw [← h1]
  congr 2
  exact Subtype.ext hker

end J7
p2m_reactivate "P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_scheme_nilpPoints_equiv_subtype_act_pow_mem_span_and_isClosedImmersion_toProjSpace.D4.J7 P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_scheme_nilpPoints_equiv_subtype_act_pow_mem_span_and_isClosedImmersion_toProjSpace.D4"

theorem exists_Mpoint_of_Hpoint {Φ : FormalODModule p K₀} (hΦ4 : Φ.HasHeight 4) (ι : Zp2 p →+* WittVector p k) (n m : ℕ)
    {H : Scheme.{0}} {q : H ⟶ Spec (CommRingCat.of K₀)}
    (pt : ∀ (S : Type) [CommRing S] [Algebra K₀ S],
      {I : Ideal (MvPowerSeries (Fin 2) S) // PZ K₀ Φ (n + m) (4 * n) S I} ≃
        {g : Spec (CommRingCat.of S) ⟶ H // g ≫ q = Spec.map (CommRingCat.ofHom (algebraMap K₀ S))})
    (hmap : ∀ (S S' : Type) [CommRing S] [CommRing S'] [Algebra K₀ S] [Algebra K₀ S'] (φ : S →ₐ[K₀] S')
      (I : {I : Ideal (MvPowerSeries (Fin 2) S) // PZ K₀ Φ (n + m) (4 * n) S I}),
      PZ K₀ Φ (n + m) (4 * n) S' (I.1.map (MvPowerSeries.map (φ : S →+* S'))))
    (hnat : ∀ (S S' : Type) [CommRing S] [CommRing S'] [Algebra K₀ S] [Algebra K₀ S'] (φ : S →ₐ[K₀] S')
      (I : {I : Ideal (MvPowerSeries (Fin 2) S) // PZ K₀ Φ (n + m) (4 * n) S I}),
      (pt S' ⟨I.1.map (MvPowerSeries.map (φ : S →+* S')), hmap S S' φ I⟩).1 =
        Spec.map (CommRingCat.ofHom (φ : S →+* S')) ≫ (pt S I).1)
    (M : ModuliPackage.{0, 0} p (WittVector p k)) (hM : M.IsZariskiSheaf)
    (η : ∀ (B : Type) [CommRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)), Rigidified p Φ B → M.obj B ψ hB)
    (hη1 : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B))
      (t t' : Rigidified p Φ B), t.IsAdmissible ι ψ → t'.IsAdmissible ι ψ → (η B ψ hB t = η B ψ hB t' ↔ t.IsIsomorphic t'))
    (hη2 : ∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] (ψ : WittVector p k →+* B)
      (ψ' : WittVector p k →+* B') (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (f : B →+* B')
      (hf : f.comp ψ = ψ') (t : Rigidified p Φ B), t.IsAdmissible ι ψ → η B' ψ' hB' (t.map f) = M.map hB hB' f hf (η B ψ hB t))
    (S : Type) [CommRing S] [IsNoetherianRing S] [Algebra K₀ S] (hS : IsNilpotent (p : S))
    (φ : Spec (CommRingCat.of S) ⟶ H) (hφ : φ ≫ q = Spec.map (CommRingCat.ofHom (algebraMap K₀ S)))
    (hsp : SpecialAt Φ ι S ((pt S).symm ⟨φ, hφ⟩).1) :
    ∃ x : M.obj S (ψof S) hS, Pnm ι M η n m S hS x ∧ Compat hΦ4 ι n m pt hmap M η S hS φ x := by
  classical
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := ((pt S).symm ⟨φ, hφ⟩).2

  obtain ⟨r, g, hspan, hloc⟩ :=
    CerednikDrinfeld.FormalODModule.exists_cover_isIsogenyOfHeight_span_range_eq_map_of_subgroup_ideal p hS
      (Φ.map (algebraMap K₀ S)) ((pt S).symm ⟨φ, hφ⟩).1 (4 * n) h1 h2 h3 h4 h5 h6 h7 h8
  choose Y ρ hY hρ using hloc
  have hL : ∀ i, IsNilpotent (p : (Localization.Away (g i))) := fun i => isNilpotent_p (k := k) _
  haveI hLN : ∀ i, IsNoetherianRing (Localization.Away (g i)) := fun i =>
    IsLocalization.isNoetherianRing (Submonoid.powers (g i)) _ inferInstance
  have hY' : ∀ i, FormalODModule.IsIsogenyOfHeight (Φ.map (algebraMap K₀ (Localization.Away (g i)))) (Y i) (ρ i) (4 * n) := by
    intro i
    have := hY i
    rwa [FormalODModule.map_map, ← IsScalarTower.algebraMap_eq] at this
  have hspY : ∀ i, (Y i).IsSpecial (structureMap ι (ψof (Localization.Away (g i)))) := fun i =>
    hsp (Localization.Away (g i)) (J7.algOf (p := p) (k := k) S (Localization.Away (g i))) (Y i) (ρ i) (hY' i).1 (hρ i)
  have ht : ∀ i, (J7.tripleOf (Φ := Φ) (Y i) n (ρ i)).IsAdmissible ι (ψof (Localization.Away (g i))) := fun i =>
    J7.tripleOf_isAdmissible hΦ4 ι (Y i) n (ρ i) (hY' i) (hspY i)
  have hcont : ∀ i j, ((J7.tripleOf (Φ := Φ) (Y i) n (ρ i)).Φbar (ψof (Localization.Away (g i)))).act ((p : Zp2 p) ^ (n + m)) j ∈ Ideal.span (Set.range (J7.tripleOf (Φ := Φ) (Y i) n (ρ i)).ρ) := by
    intro i
    apply J7.tripleOf_hcont
    intro j
    rw [hρ i, IsScalarTower.algebraMap_eq K₀ S (Localization.Away (g i)), ← FormalODModule.map_map, FormalODModule.map_act]
    exact Ideal.mem_map_of_mem _ (h9 j)
  have ht_via : ∀ i, (J7.tripleOf (Φ := Φ) (Y i) n (ρ i)).IsAdmissible ι (ψvia S (Localization.Away (g i))) := fun i => by rw [ψvia_eq S]; exact ht i
  have hcont_via : ∀ i j, ((J7.tripleOf (Φ := Φ) (Y i) n (ρ i)).Φbar (ψvia S (Localization.Away (g i)))).act ((p : Zp2 p) ^ (n + m)) j ∈ Ideal.span (Set.range (J7.tripleOf (Φ := Φ) (Y i) n (ρ i)).ρ) :=
    fun i => by rw [ψvia_eq S]; exact hcont i

  haveI hjiAll : ∀ i j, IsLocalization.Away (g j * g i) (Localization.Away (g i * g j)) := fun i j => by
    rw [mul_comm]; infer_instance
  have hL₂ : ∀ i j, IsNilpotent (p : (Localization.Away (g i * g j))) := fun i j => isNilpotent_p (k := k) _
  obtain ⟨x, hx⟩ := (hM S (ψof S) hS r g hspan (fun i => (Localization.Away (g i))) hL (fun i j => (Localization.Away (g i * g j))) hL₂
      (fun i j => (awayRightAlg (p := p) (k := k) (g i) (g j) (Localization.Away (g i * g j)) : (Localization.Away (g i)) →+* (Localization.Away (g i * g j))))
      (fun i j => (awayRightAlg (p := p) (k := k) (g j) (g i) (Localization.Away (g i * g j)) : (Localization.Away (g j)) →+* (Localization.Away (g i * g j))))
      (fun i j b => IsLocalization.Away.awayToAwayRight_eq (g i) (g j) b)
      (fun i j b => IsLocalization.Away.awayToAwayRight_eq (g j) (g i) b)).2
    (fun i => η (Localization.Away (g i)) (ψvia S (Localization.Away (g i))) (hL i) (J7.tripleOf (Φ := Φ) (Y i) n (ρ i)))
    (by
      intro i j
      haveI : IsNoetherianRing (Localization.Away (g i * g j)) :=
        IsLocalization.isNoetherianRing (Submonoid.powers (g i * g j)) _ inferInstance
      have hai : (awayRightAlg (p := p) (k := k) (g i) (g j) (Localization.Away (g i * g j)) : (Localization.Away (g i)) →+* (Localization.Away (g i * g j))).comp (ψvia S (Localization.Away (g i))) =
          ψvia (p := p) (k := k) S (Localization.Away (g i * g j)) := by
        show ((awayRightAlg (p := p) (k := k) (g i) (g j) (Localization.Away (g i * g j)) : (Localization.Away (g i)) →+* (Localization.Away (g i * g j))).comp (algebraMap S _)).comp
          (ψof (p := p) (k := k) S) = (algebraMap S (Localization.Away (g i * g j))).comp (ψof (p := p) (k := k) S)
        rw [awayRightAlg_comp_algebraMap]
      have haj : (awayRightAlg (p := p) (k := k) (g j) (g i) (Localization.Away (g i * g j)) : (Localization.Away (g j)) →+* (Localization.Away (g i * g j))).comp (ψvia S (Localization.Away (g j))) =
          ψvia (p := p) (k := k) S (Localization.Away (g i * g j)) := by
        show ((awayRightAlg (p := p) (k := k) (g j) (g i) (Localization.Away (g i * g j)) : (Localization.Away (g j)) →+* (Localization.Away (g i * g j))).comp (algebraMap S _)).comp
          (ψof (p := p) (k := k) S) = (algebraMap S (Localization.Away (g i * g j))).comp (ψof (p := p) (k := k) S)
        rw [awayRightAlg_comp_algebraMap]
      rw [← hη2 (Localization.Away (g i)) (Localization.Away (g i * g j)) (ψvia S (Localization.Away (g i))) (ψvia S (Localization.Away (g i * g j))) (hL i) (hL₂ i j) _ hai _ (ht_via i),
        ← hη2 (Localization.Away (g j)) (Localization.Away (g i * g j)) (ψvia S (Localization.Away (g j))) (ψvia S (Localization.Away (g i * g j))) (hL j) (hL₂ i j) _ haj _ (ht_via j)]
      exact (hη1 (Localization.Away (g i * g j)) (ψvia S (Localization.Away (g i * g j))) (hL₂ i j) _ _
        (by rw [ψvia_eq S]; exact isAdmissible_map_alg ι _ _ (ht i))
        (by rw [ψvia_eq S]; exact isAdmissible_map_alg ι _ _ (ht j))).mpr
        (J7.isIsomorphic_of_kerIdeal_eq ι _ _ (isAdmissible_map_alg ι _ _ (ht i)) (isAdmissible_map_alg ι _ _ (ht j)) rfl
          (by rw [J7.kerIdeal_tripleOf_map _ (Y i) n (ρ i) ((pt S).symm ⟨φ, hφ⟩).1 _ (hρ i),
                J7.kerIdeal_tripleOf_map _ (Y j) n (ρ j) ((pt S).symm ⟨φ, hφ⟩).1 _ (hρ j),
                awayRightAlg_comp_algebraMap, awayRightAlg_comp_algebraMap])))
  refine ⟨x, ⟨r, g, hspan, ?_⟩, ?_⟩
  ·
    intro i L _ _ _ _ hL'
    let e : (Localization.Away (g i)) →+* L :=
      IsLocalization.Away.lift (g i) (IsLocalization.Away.algebraMap_isUnit (S := L) (g i))
    have he : e.comp (algebraMap S (Localization.Away (g i))) = algebraMap S L := IsLocalization.Away.lift_comp _ _
    have hf : e.comp (ψvia S (Localization.Away (g i))) = ψvia (p := p) (k := k) S L := by
      show (e.comp (algebraMap S (Localization.Away (g i)))).comp (ψof (p := p) (k := k) S) = (algebraMap S L).comp (ψof (p := p) (k := k) S)
      rw [he]
    refine ⟨(J7.tripleOf (Φ := Φ) (Y i) n (ρ i)).map e, ?_, rfl, ?_, ?_⟩
    · have := Rigidified.IsAdmissible.map_ringHom ι (ψvia S (Localization.Away (g i))) e _ (ht_via i)
      rwa [hf] at this
    · have := J7.hcont_map_ringHom (ψvia S (Localization.Away (g i))) e (J7.tripleOf (Φ := Φ) (Y i) n (ρ i)) (n + m) (hcont_via i)
      rwa [hf] at this
    · rw [hη2 (Localization.Away (g i)) L (ψvia S (Localization.Away (g i))) (ψvia S L) (hL i) hL' e hf _ (ht_via i), ← hx i, ← M.map_comp]
      exact map_congr M hS hL' _ _ _ _ he x
  ·
    intro g₀ t ht0 hn0 hcont0 hηt
    haveI hN0 : IsNoetherianRing (Localization.Away g₀) := IsLocalization.isNoetherianRing (Submonoid.powers g₀) _ inferInstance
    have hspan0 : Ideal.span (Set.range (fun i => algebraMap S (Localization.Away g₀) (g i))) = ⊤ := by
      rw [← ideal_map_span_range, hspan, Ideal.map_top]
    apply glue_opens_unique (fun i => (PrimeSpectrum.basicOpen (algebraMap S (Localization.Away g₀) (g i)) : (Spec (CommRingCat.of (Localization.Away g₀))).Opens))
      (iSup_basicOpen_eq_top _ hspan0)
    intro i
    haveI hNp : IsNoetherianRing (Localization.Away (algebraMap S (Localization.Away g₀) (g i))) :=
      IsLocalization.isNoetherianRing (Submonoid.powers (algebraMap S (Localization.Away g₀) (g i))) _ inferInstance
    haveI hTp : IsScalarTower K₀ S (Localization.Away (algebraMap S (Localization.Away g₀) (g i))) := IsScalarTower.of_algebraMap_eq (fun x =>
      (IsScalarTower.algebraMap_apply K₀ (Localization.Away g₀) (Localization.Away (algebraMap S (Localization.Away g₀) (g i))) x).trans
        ((congrArg (algebraMap (Localization.Away g₀) (Localization.Away (algebraMap S (Localization.Away g₀) (g i)))) (IsScalarTower.algebraMap_apply K₀ S (Localization.Away g₀) x)).trans
          (IsScalarTower.algebraMap_apply S (Localization.Away g₀) (Localization.Away (algebraMap S (Localization.Away g₀) (g i))) _).symm))
    have hLp : IsNilpotent (p : (Localization.Away (algebraMap S (Localization.Away g₀) (g i)))) := isNilpotent_p (k := k) _
    have hfac := IsOpenImmersion.isoOfRangeEq_hom_fac
      (Scheme.Opens.ι (X := Spec (CommRingCat.of (Localization.Away g₀))) (PrimeSpectrum.basicOpen (algebraMap S (Localization.Away g₀) (g i))))
      (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away g₀) (Localization.Away (algebraMap S (Localization.Away g₀) (g i))))))
      (by simp only [Scheme.Opens.range_ι]; exact (PrimeSpectrum.localization_away_comap_range _ _).symm)
    rw [← hfac, Category.assoc, Category.assoc]
    congr 1

    have hunit : IsUnit (algebraMap S (Localization.Away (algebraMap S (Localization.Away g₀) (g i))) (g i)) := by
      rw [IsScalarTower.algebraMap_apply S (Localization.Away g₀) (Localization.Away (algebraMap S (Localization.Away g₀) (g i))) (g i)]
      exact IsLocalization.Away.algebraMap_isUnit (S := (Localization.Away (algebraMap S (Localization.Away g₀) (g i)))) (algebraMap S (Localization.Away g₀) (g i))
    have hf0 : (J7.algOf (p := p) (k := k) (Localization.Away g₀) (Localization.Away (algebraMap S (Localization.Away g₀) (g i))) : (Localization.Away g₀) →+* (Localization.Away (algebraMap S (Localization.Away g₀) (g i)))).comp (ψvia S (Localization.Away g₀)) = ψvia (p := p) (k := k) S (Localization.Away (algebraMap S (Localization.Away g₀) (g i))) := by
      show ((algebraMap (Localization.Away g₀) (Localization.Away (algebraMap S (Localization.Away g₀) (g i)))).comp (algebraMap S (Localization.Away g₀))).comp (ψof (p := p) (k := k) S) =
        (algebraMap S (Localization.Away (algebraMap S (Localization.Away g₀) (g i)))).comp (ψof (p := p) (k := k) S)
      rw [← IsScalarTower.algebraMap_eq S (Localization.Away g₀) (Localization.Away (algebraMap S (Localization.Away g₀) (g i)))]
    have hfi : (J7.liftAlg (p := p) (k := k) (g i) (Localization.Away (algebraMap S (Localization.Away g₀) (g i))) hunit : (Localization.Away (g i)) →+* (Localization.Away (algebraMap S (Localization.Away g₀) (g i)))).comp (ψvia S (Localization.Away (g i))) = ψvia (p := p) (k := k) S (Localization.Away (algebraMap S (Localization.Away g₀) (g i))) := by
      show ((J7.liftAlg (p := p) (k := k) (g i) (Localization.Away (algebraMap S (Localization.Away g₀) (g i))) hunit : (Localization.Away (g i)) →+* (Localization.Away (algebraMap S (Localization.Away g₀) (g i)))).comp (algebraMap S (Localization.Away (g i)))).comp
        (ψof (p := p) (k := k) S) = (algebraMap S (Localization.Away (algebraMap S (Localization.Away g₀) (g i)))).comp (ψof (p := p) (k := k) S)
      rw [J7.liftAlg_comp_algebraMap]
    have ht0_via : t.IsAdmissible ι (ψvia S (Localization.Away g₀)) := by rw [ψvia_eq S]; exact ht0
    have e0 : η (Localization.Away (algebraMap S (Localization.Away g₀) (g i))) (ψvia S (Localization.Away (algebraMap S (Localization.Away g₀) (g i)))) hLp (t.map (J7.algOf (p := p) (k := k) (Localization.Away g₀) (Localization.Away (algebraMap S (Localization.Away g₀) (g i))) : (Localization.Away g₀) →+* (Localization.Away (algebraMap S (Localization.Away g₀) (g i))))) =
        M.map hS hLp (algebraMap S (Localization.Away (algebraMap S (Localization.Away g₀) (g i)))) rfl x := by
      rw [hη2 (Localization.Away g₀) (Localization.Away (algebraMap S (Localization.Away g₀) (g i))) (ψvia S (Localization.Away g₀)) (ψvia S (Localization.Away (algebraMap S (Localization.Away g₀) (g i)))) (isNilpotent_p (k := k) _) hLp _ hf0 t ht0_via, hηt, ← M.map_comp]
      exact map_congr M hS hLp _ _ _ _ (IsScalarTower.algebraMap_eq S (Localization.Away g₀) (Localization.Away (algebraMap S (Localization.Away g₀) (g i)))).symm x
    have eI : η (Localization.Away (algebraMap S (Localization.Away g₀) (g i))) (ψvia S (Localization.Away (algebraMap S (Localization.Away g₀) (g i)))) hLp ((J7.tripleOf (Φ := Φ) (Y i) n (ρ i)).map (J7.liftAlg (p := p) (k := k) (g i) (Localization.Away (algebraMap S (Localization.Away g₀) (g i))) hunit : (Localization.Away (g i)) →+* (Localization.Away (algebraMap S (Localization.Away g₀) (g i))))) =
        M.map hS hLp (algebraMap S (Localization.Away (algebraMap S (Localization.Away g₀) (g i)))) rfl x := by
      rw [hη2 (Localization.Away (g i)) (Localization.Away (algebraMap S (Localization.Away g₀) (g i))) (ψvia S (Localization.Away (g i))) (ψvia S (Localization.Away (algebraMap S (Localization.Away g₀) (g i)))) (hL i) hLp _ hfi _ (ht_via i), ← hx i, ← M.map_comp]
      exact map_congr M hS hLp _ _ _ _ (J7.liftAlg_comp_algebraMap (p := p) (k := k) (g i) (Localization.Away (algebraMap S (Localization.Away g₀) (g i))) hunit) x
    have hiso : (t.map (J7.algOf (p := p) (k := k) (Localization.Away g₀) (Localization.Away (algebraMap S (Localization.Away g₀) (g i))) : (Localization.Away g₀) →+* (Localization.Away (algebraMap S (Localization.Away g₀) (g i))))).IsIsomorphic
        ((J7.tripleOf (Φ := Φ) (Y i) n (ρ i)).map (J7.liftAlg (p := p) (k := k) (g i) (Localization.Away (algebraMap S (Localization.Away g₀) (g i))) hunit : (Localization.Away (g i)) →+* (Localization.Away (algebraMap S (Localization.Away g₀) (g i))))) :=
      (hη1 (Localization.Away (algebraMap S (Localization.Away g₀) (g i))) (ψvia S (Localization.Away (algebraMap S (Localization.Away g₀) (g i)))) hLp _ _
        (by rw [ψvia_eq S]; exact isAdmissible_map_alg ι (J7.algOf (p := p) (k := k) (Localization.Away g₀) (Localization.Away (algebraMap S (Localization.Away g₀) (g i)))) t ht0)
        (by rw [ψvia_eq S]; exact isAdmissible_map_alg ι (J7.liftAlg (p := p) (k := k) (g i) (Localization.Away (algebraMap S (Localization.Away g₀) (g i))) hunit) _ (ht i))).mp (e0.trans eI.symm)
    have ei := pointOfTriple_map hΦ4 ι n m pt hmap hnat (J7.algOf (p := p) (k := k) (Localization.Away g₀) (Localization.Away (algebraMap S (Localization.Away g₀) (g i)))) t ht0 hn0 hcont0
      (isAdmissible_map_alg ι _ t ht0) hn0 (hcont_map_alg _ t (n + m) hcont0)
    have hkeri : kerIdeal (k := k) ((J7.tripleOf (Φ := Φ) (Y i) n (ρ i)).map (J7.liftAlg (p := p) (k := k) (g i) (Localization.Away (algebraMap S (Localization.Away g₀) (g i))) hunit : (Localization.Away (g i)) →+* (Localization.Away (algebraMap S (Localization.Away g₀) (g i))))) =
        ((pt S).symm ⟨φ, hφ⟩).1.map (MvPowerSeries.map (J7.algOf (p := p) (k := k) S (Localization.Away (algebraMap S (Localization.Away g₀) (g i))) : S →+* (Localization.Away (algebraMap S (Localization.Away g₀) (g i))))) := by
      rw [J7.kerIdeal_tripleOf_map _ (Y i) n (ρ i) ((pt S).symm ⟨φ, hφ⟩).1 _ (hρ i), J7.liftAlg_comp_algebraMap]
      rfl
    have hPi := J7.pointOfTriple_eq hΦ4 ι n m pt hmap hnat S φ hφ (J7.algOf (p := p) (k := k) S (Localization.Away (algebraMap S (Localization.Away g₀) (g i)))) _
      (isAdmissible_map_alg ι _ _ (ht i)) rfl (hcont_map_alg _ _ (n + m) (hcont i)) hkeri
    have hcomp : (J7.algOf (p := p) (k := k) (Localization.Away g₀) (Localization.Away (algebraMap S (Localization.Away g₀) (g i))) : (Localization.Away g₀) →+* (Localization.Away (algebraMap S (Localization.Away g₀) (g i)))).comp (algebraMap S (Localization.Away g₀)) = (J7.algOf (p := p) (k := k) S (Localization.Away (algebraMap S (Localization.Away g₀) (g i))) : S →+* (Localization.Away (algebraMap S (Localization.Away g₀) (g i)))) := by
      rw [J7.algOf_coe, J7.algOf_coe, ← IsScalarTower.algebraMap_eq]
    change Spec.map (CommRingCat.ofHom (J7.algOf (p := p) (k := k) (Localization.Away g₀) (Localization.Away (algebraMap S (Localization.Away g₀) (g i))) : (Localization.Away g₀) →+* (Localization.Away (algebraMap S (Localization.Away g₀) (g i))))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀))) ≫ φ =
      Spec.map (CommRingCat.ofHom (J7.algOf (p := p) (k := k) (Localization.Away g₀) (Localization.Away (algebraMap S (Localization.Away g₀) (g i))) : (Localization.Away g₀) →+* (Localization.Away (algebraMap S (Localization.Away g₀) (g i))))) ≫ (pointOfTriple hΦ4 ι n m pt hmap t ht0 hn0 hcont0).1
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp, ← hPi, ← ei]
    exact (pointOfTriple_congr hΦ4 ι n m pt hmap _ _ _ _ _ _ _ _ hiso).symm

end D4
p2m_reactivate "P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_scheme_nilpPoints_equiv_subtype_act_pow_mem_span_and_isClosedImmersion_toProjSpace.D4.J7 P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_scheme_nilpPoints_equiv_subtype_act_pow_mem_span_and_isClosedImmersion_toProjSpace.D4"

namespace D4

open MvPowerSeries

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p]

local notation "K₀" => (WittVector p k ⧸ pIdeal p (WittVector p k))

theorem span_range_mul_eq_top {S : Type} [CommRing S] {r r' : ℕ} (f : Fin r → S) (f' : Fin r' → S)
    (hf : Ideal.span (Set.range f) = ⊤) (hf' : Ideal.span (Set.range f') = ⊤) :
    Ideal.span (Set.range (fun c : Fin (r * r') => f (finProdFinEquiv.symm c).1 * f' (finProdFinEquiv.symm c).2)) = ⊤ := by
  have key : Ideal.span (Set.range f) * Ideal.span (Set.range f') ≤
      Ideal.span (Set.range (fun c : Fin (r * r') => f (finProdFinEquiv.symm c).1 * f' (finProdFinEquiv.symm c).2)) := by
    rw [Ideal.span_mul_span']
    apply Ideal.span_le.mpr
    rintro _ ⟨a, ⟨i, rfl⟩, b, ⟨j, rfl⟩, rfl⟩
    exact Ideal.subset_span ⟨finProdFinEquiv (i, j), by simp⟩
  rw [hf, hf', Ideal.top_mul] at key
  exact eq_top_iff.mpr key

theorem span_eq_of_kerIdeal_eq {Φ : FormalODModule p K₀} {L : Type} [CommRing L] [Algebra K₀ L] (t t' : Rigidified p Φ L)
    (h : kerIdeal (k := k) t = kerIdeal (k := k) t') : Ideal.span (Set.range t.ρ) = Ideal.span (Set.range t'.ρ) := by
  have key : ∀ I : Ideal (MvPowerSeries (Fin 2) (L ⧸ pIdeal p L)),
      (I.map (MvPowerSeries.map (quotAlgEquiv (p := p) (k := k) L).symm.toRingEquiv.toRingHom)).map
        (MvPowerSeries.map (quotAlgEquiv (p := p) (k := k) L).toRingEquiv.toRingHom) = I := by
    intro I
    rw [Ideal.map_map, ← MvPowerSeries.map_comp]
    have : (quotAlgEquiv (p := p) (k := k) L).toRingEquiv.toRingHom.comp (quotAlgEquiv (p := p) (k := k) L).symm.toRingEquiv.toRingHom = RingHom.id _ := by
      ext x; exact (quotAlgEquiv (p := p) (k := k) L).apply_symm_apply x
    rw [this, MvPowerSeries.map_id, Ideal.map_id]
  have := congrArg (fun I => Ideal.map (MvPowerSeries.map (quotAlgEquiv (p := p) (k := k) L).toRingEquiv.toRingHom) I) h
  simpa only [kerIdeal, key] using this

theorem Compat.unique_M {Φ : FormalODModule p K₀} (hΦ4 : Φ.HasHeight 4) (ι : Zp2 p →+* WittVector p k) (n m : ℕ)
    {H : Scheme.{0}} {q : H ⟶ Spec (CommRingCat.of K₀)}
    (pt : ∀ (S : Type) [CommRing S] [Algebra K₀ S],
      {I : Ideal (MvPowerSeries (Fin 2) S) // PZ K₀ Φ (n + m) (4 * n) S I} ≃
        {g : Spec (CommRingCat.of S) ⟶ H // g ≫ q = Spec.map (CommRingCat.ofHom (algebraMap K₀ S))})
    (hmap : ∀ (S S' : Type) [CommRing S] [CommRing S'] [Algebra K₀ S] [Algebra K₀ S'] (φ : S →ₐ[K₀] S')
      (I : {I : Ideal (MvPowerSeries (Fin 2) S) // PZ K₀ Φ (n + m) (4 * n) S I}),
      PZ K₀ Φ (n + m) (4 * n) S' (I.1.map (MvPowerSeries.map (φ : S →+* S'))))
    (hnat : ∀ (S S' : Type) [CommRing S] [CommRing S'] [Algebra K₀ S] [Algebra K₀ S'] (φ : S →ₐ[K₀] S')
      (I : {I : Ideal (MvPowerSeries (Fin 2) S) // PZ K₀ Φ (n + m) (4 * n) S I}),
      (pt S' ⟨I.1.map (MvPowerSeries.map (φ : S →+* S')), hmap S S' φ I⟩).1 =
        Spec.map (CommRingCat.ofHom (φ : S →+* S')) ≫ (pt S I).1)
    (M : ModuliPackage.{0, 0} p (WittVector p k)) (hM : M.IsZariskiSheaf)
    (η : ∀ (B : Type) [CommRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)), Rigidified p Φ B → M.obj B ψ hB)
    (hη1 : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B))
      (t t' : Rigidified p Φ B), t.IsAdmissible ι ψ → t'.IsAdmissible ι ψ → (η B ψ hB t = η B ψ hB t' ↔ t.IsIsomorphic t'))
    (hη2 : ∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] (ψ : WittVector p k →+* B)
      (ψ' : WittVector p k →+* B') (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (f : B →+* B')
      (hf : f.comp ψ = ψ') (t : Rigidified p Φ B), t.IsAdmissible ι ψ → η B' ψ' hB' (t.map f) = M.map hB hB' f hf (η B ψ hB t))
    (S : Type) [CommRing S] [IsNoetherianRing S] [Algebra K₀ S] (hS : IsNilpotent (p : S))
    (φ : Spec (CommRingCat.of S) ⟶ H) (x x' : M.obj S (ψof S) hS)
    (hφ : Compat hΦ4 ι n m pt hmap M η S hS φ x) (hφ' : Compat hΦ4 ι n m pt hmap M η S hS φ x')
    (hx : Pnm ι M η n m S hS x) (hx' : Pnm ι M η n m S hS x') : x = x' := by
  classical
  obtain ⟨r, f, hspan, hloc⟩ := hx
  obtain ⟨r', f', hspan', hloc'⟩ := hx'

  let h : Fin (r * r') → S := fun c => f (finProdFinEquiv.symm c).1 * f' (finProdFinEquiv.symm c).2
  have hh : Ideal.span (Set.range h) = ⊤ := span_range_mul_eq_top f f' hspan hspan'
  haveI hcomm : ∀ c d : Fin (r * r'), IsLocalization.Away (h d * h c) (Localization.Away (h c * h d)) := fun c d => by
    rw [mul_comm]; infer_instance
  refine (hM S (ψof S) hS (r * r') h hh (fun c => Localization.Away (h c)) (fun c => isNilpotent_p (k := k) _)
    (fun c d => Localization.Away (h c * h d)) (fun c d => isNilpotent_p (k := k) _)
    (fun c d => IsLocalization.Away.awayToAwayRight (h c) (h d))
    (fun c d => IsLocalization.Away.awayToAwayRight (h d) (h c))
    (fun c d b => IsLocalization.Away.awayToAwayRight_eq _ _ b)
    (fun c d b => IsLocalization.Away.awayToAwayRight_eq _ _ b)).1 x x' ?_
  intro c

  set i := (finProdFinEquiv.symm c).1 with hi
  set j := (finProdFinEquiv.symm c).2 with hj
  let Lc := Localization.Away (h c)
  haveI : IsNoetherianRing Lc := IsLocalization.isNoetherianRing (Submonoid.powers (h c)) _ inferInstance
  haveI : IsNoetherianRing (Localization.Away (f i)) := IsLocalization.isNoetherianRing (Submonoid.powers (f i)) _ inferInstance
  haveI : IsNoetherianRing (Localization.Away (f' j)) := IsLocalization.isNoetherianRing (Submonoid.powers (f' j)) _ inferInstance
  haveI hij : IsLocalization.Away (f i * f' j) Lc := by show IsLocalization.Away (h c) Lc; infer_instance
  haveI hji : IsLocalization.Away (f' j * f i) Lc := by rw [mul_comm]; exact hij

  obtain ⟨t, ht, hn, hcont, hηt⟩ := hloc i (Localization.Away (f i)) (isNilpotent_p (k := k) _)
  obtain ⟨t', ht', hn', hcont', hηt'⟩ := hloc' j (Localization.Away (f' j)) (isNilpotent_p (k := k) _)
  let ai : Localization.Away (f i) →ₐ[K₀] Lc := awayRightAlg (f i) (f' j) Lc
  let aj : Localization.Away (f' j) →ₐ[K₀] Lc := awayRightAlg (f' j) (f i) Lc
  have hai : (ai : Localization.Away (f i) →+* Lc).comp (ψvia S (Localization.Away (f i))) = ψvia (p := p) (k := k) S Lc := by
    show ((ai : Localization.Away (f i) →+* Lc).comp (algebraMap S _)).comp (ψof (p := p) (k := k) S) = (algebraMap S Lc).comp (ψof (p := p) (k := k) S)
    rw [awayRightAlg_comp_algebraMap]
  have haj : (aj : Localization.Away (f' j) →+* Lc).comp (ψvia S (Localization.Away (f' j))) = ψvia (p := p) (k := k) S Lc := by
    show ((aj : Localization.Away (f' j) →+* Lc).comp (algebraMap S _)).comp (ψof (p := p) (k := k) S) = (algebraMap S Lc).comp (ψof (p := p) (k := k) S)
    rw [awayRightAlg_comp_algebraMap]

  have hηi : η Lc (ψvia S Lc) (isNilpotent_p (k := k) _) (t.map (ai : Localization.Away (f i) →+* Lc)) =
      M.map hS (isNilpotent_p (k := k) _) (algebraMap S Lc) rfl x := by
    rw [hη2 _ _ _ _ (isNilpotent_p (k := k) _) (isNilpotent_p (k := k) Lc) (ai : Localization.Away (f i) →+* Lc) hai t ht, hηt,
      ← M.map_comp]
    exact map_congr M hS (isNilpotent_p (k := k) Lc) _ _ _ _ (awayRightAlg_comp_algebraMap (p := p) (k := k) (f i) (f' j) Lc) x
  have hηj : η Lc (ψvia S Lc) (isNilpotent_p (k := k) _) (t'.map (aj : Localization.Away (f' j) →+* Lc)) =
      M.map hS (isNilpotent_p (k := k) _) (algebraMap S Lc) rfl x' := by
    rw [hη2 _ _ _ _ (isNilpotent_p (k := k) _) (isNilpotent_p (k := k) Lc) (aj : Localization.Away (f' j) →+* Lc) haj t' ht', hηt',
      ← M.map_comp]
    exact map_congr M hS (isNilpotent_p (k := k) Lc) _ _ _ _ (awayRightAlg_comp_algebraMap (p := p) (k := k) (f' j) (f i) Lc) x'

  have htv : t.IsAdmissible ι (ψof (Localization.Away (f i))) := by rw [← ψvia_eq S]; exact ht
  have htv' : t'.IsAdmissible ι (ψof (Localization.Away (f' j))) := by rw [← ψvia_eq S]; exact ht'
  have hcv : ∀ jj, (t.Φbar (ψof (Localization.Away (f i)))).act ((p : Zp2 p) ^ (n + m)) jj ∈ Ideal.span (Set.range t.ρ) := by
    rw [← ψvia_eq S]; exact hcont
  have hcv' : ∀ jj, (t'.Φbar (ψof (Localization.Away (f' j)))).act ((p : Zp2 p) ^ (n + m)) jj ∈ Ideal.span (Set.range t'.ρ) := by
    rw [← ψvia_eq S]; exact hcont'
  have hA_i := isAdmissible_map_alg ι ai t htv
  have hA_j := isAdmissible_map_alg ι aj t' htv'
  have hC_i := hcont_map_alg ai t (n + m) hcv
  have hC_j := hcont_map_alg aj t' (n + m) hcv'

  have e1 := hφ (h c) (t.map (ai : Localization.Away (f i) →+* Lc)) hA_i hn hC_i hηi
  have e2 := hφ' (h c) (t'.map (aj : Localization.Away (f' j) →+* Lc)) hA_j hn' hC_j hηj
  have hpt : (pointOfTriple hΦ4 ι n m pt hmap (t.map (ai : Localization.Away (f i) →+* Lc)) hA_i hn hC_i).1 =
      (pointOfTriple hΦ4 ι n m pt hmap (t'.map (aj : Localization.Away (f' j) →+* Lc)) hA_j hn' hC_j).1 := by rw [← e1, ← e2]

  have hker : kerIdeal (k := k) (t.map (ai : Localization.Away (f i) →+* Lc)) = kerIdeal (k := k) (t'.map (aj : Localization.Away (f' j) →+* Lc)) := by
    have := (pt Lc).injective (Subtype.ext hpt)
    exact congrArg Subtype.val this
  have hiso := isIsomorphic_of_span_eq ι _ _ hA_i hA_j (hn.trans hn'.symm) (span_eq_of_kerIdeal_eq _ _ hker)
  have hA_i' : (t.map (ai : Localization.Away (f i) →+* Lc)).IsAdmissible ι (ψvia S Lc) := by rw [ψvia_eq S]; exact hA_i
  have hA_j' : (t'.map (aj : Localization.Away (f' j) →+* Lc)).IsAdmissible ι (ψvia S Lc) := by rw [ψvia_eq S]; exact hA_j
  have := (hη1 Lc (ψvia S Lc) (isNilpotent_p (k := k) _) _ _ hA_i' hA_j').mpr hiso
  rw [hηi, hηj] at this
  exact this

end D4
p2m_reactivate "P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_scheme_nilpPoints_equiv_subtype_act_pow_mem_span_and_isClosedImmersion_toProjSpace.D4.J7 P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_scheme_nilpPoints_equiv_subtype_act_pow_mem_span_and_isClosedImmersion_toProjSpace.D4"

namespace D4

open MvPowerSeries

noncomputable def ccAlgHom (B : Type) [CommRing B] : MvPowerSeries (Fin 2) B →ₐ[B] B :=
  { toRingHom := MvPowerSeries.constantCoeff
    commutes' := fun r => by
      show MvPowerSeries.constantCoeff (algebraMap B (MvPowerSeries (Fin 2) B) r) = r
      rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, MvPowerSeries.constantCoeff_C] }

theorem span_range_seriesId (B : Type) [CommRing B] :
    Ideal.span (Set.range (Series.id B)) = RingHom.ker (ccAlgHom B).toRingHom := by
  show Ideal.span (Set.range (fun i : Fin 2 => (X i : MvPowerSeries (Fin 2) B))) = RingHom.ker MvPowerSeries.constantCoeff
  exact MvPowerSeries.span_range_X_eq_ker_constantCoeff 2

noncomputable def kerAlgebraIdEquiv (B : Type) [CommRing B] : FormalODModule.KerAlgebra (Series.id B) ≃ₐ[B] B :=
  (Ideal.quotientEquivAlgOfEq B (span_range_seriesId B)).trans
    (Ideal.quotientKerAlgEquivOfSurjective (f := ccAlgHom B) (fun b => ⟨MvPowerSeries.C b, MvPowerSeries.constantCoeff_C b⟩))

theorem hasKernelOfDegree_seriesId (B : Type) [CommRing B] : FormalODModule.HasKernelOfDegree (Series.id B) 1 := by
  refine ⟨Module.Finite.equiv (kerAlgebraIdEquiv B).symm.toLinearEquiv,
    Module.Projective.of_equiv (kerAlgebraIdEquiv B).symm.toLinearEquiv, ?_⟩
  intro κ _ f
  rw [Series.map_id]
  rw [LinearEquiv.finrank_eq (kerAlgebraIdEquiv κ).toLinearEquiv, Module.finrank_self]

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p]

local notation "K₀" => (WittVector p k ⧸ pIdeal p (WittVector p k))

theorem kerAlgebra_inputs' (Φ : FormalODModule p K₀) (hΦ4 : Φ.HasHeight 4) (N : ℕ) :
    Module.Finite K₀ (FormalODModule.KerAlgebra (Φ.act ((p : Zp2 p) ^ N))) ∧
    Module.Free K₀ (FormalODModule.KerAlgebra (Φ.act ((p : Zp2 p) ^ N))) ∧
    ∀ i, IsNilpotent (Ideal.Quotient.mk (Ideal.span (Set.range (Φ.act ((p : Zp2 p) ^ N)))) (MvPowerSeries.X i)) := by
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · subst h0
    rw [pow_zero, FormalODModule.act_one]
    have hker := hasKernelOfDegree_seriesId K₀
    haveI : Module.Finite K₀ (FormalODModule.KerAlgebra (Series.id K₀)) := hker.1
    refine ⟨hker.1, ?_, ?_⟩
    · letI : Field K₀ := fieldK0
      exact Module.Free.of_divisionRing K₀ _
    · intro i
      exact ⟨1, by rw [pow_one, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.subset_span ⟨i, rfl⟩⟩
  · exact kerAlgebra_inputs Φ hΦ4 N hpos.ne'

end D4
p2m_reactivate "P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_scheme_nilpPoints_equiv_subtype_act_pow_mem_span_and_isClosedImmersion_toProjSpace.D4.J7 P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_scheme_nilpPoints_equiv_subtype_act_pow_mem_span_and_isClosedImmersion_toProjSpace.D4"

namespace D4

open MvPowerSeries

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p]

local notation "K₀" => (WittVector p k ⧸ pIdeal p (WittVector p k))

theorem span_range_algebraMap_eq_top {S L : Type} [CommRing S] [CommRing L] [Algebra S L] {r : ℕ} (f : Fin r → S)
    (hspan : Ideal.span (Set.range f) = ⊤) : Ideal.span (Set.range (fun i => algebraMap S L (f i))) = ⊤ := by
  have := congrArg (Ideal.map (algebraMap S L)) hspan
  rwa [Ideal.map_top, ideal_map_span_range] at this

theorem compat_of_cover {Φ : FormalODModule p K₀} (hΦ4 : Φ.HasHeight 4) (ι : Zp2 p →+* WittVector p k) (n m : ℕ)
    {H : Scheme.{0}} {q : H ⟶ Spec (CommRingCat.of K₀)}
    (pt : ∀ (S : Type) [CommRing S] [Algebra K₀ S],
      {I : Ideal (MvPowerSeries (Fin 2) S) // PZ K₀ Φ (n + m) (4 * n) S I} ≃
        {g : Spec (CommRingCat.of S) ⟶ H // g ≫ q = Spec.map (CommRingCat.ofHom (algebraMap K₀ S))})
    (hmap : ∀ (S S' : Type) [CommRing S] [CommRing S'] [Algebra K₀ S] [Algebra K₀ S'] (φ : S →ₐ[K₀] S')
      (I : {I : Ideal (MvPowerSeries (Fin 2) S) // PZ K₀ Φ (n + m) (4 * n) S I}),
      PZ K₀ Φ (n + m) (4 * n) S' (I.1.map (MvPowerSeries.map (φ : S →+* S'))))
    (hnat : ∀ (S S' : Type) [CommRing S] [CommRing S'] [Algebra K₀ S] [Algebra K₀ S'] (φ : S →ₐ[K₀] S')
      (I : {I : Ideal (MvPowerSeries (Fin 2) S) // PZ K₀ Φ (n + m) (4 * n) S I}),
      (pt S' ⟨I.1.map (MvPowerSeries.map (φ : S →+* S')), hmap S S' φ I⟩).1 =
        Spec.map (CommRingCat.ofHom (φ : S →+* S')) ≫ (pt S I).1)
    (M : ModuliPackage.{0, 0} p (WittVector p k)) (hM : M.IsZariskiSheaf)
    (η : ∀ (B : Type) [CommRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)), Rigidified p Φ B → M.obj B ψ hB)
    (hη1 : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B))
      (t t' : Rigidified p Φ B), t.IsAdmissible ι ψ → t'.IsAdmissible ι ψ → (η B ψ hB t = η B ψ hB t' ↔ t.IsIsomorphic t'))
    (hη2 : ∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] (ψ : WittVector p k →+* B)
      (ψ' : WittVector p k →+* B') (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (f : B →+* B')
      (hf : f.comp ψ = ψ') (t : Rigidified p Φ B), t.IsAdmissible ι ψ → η B' ψ' hB' (t.map f) = M.map hB hB' f hf (η B ψ hB t))
    (S : Type) [CommRing S] [IsNoetherianRing S] [Algebra K₀ S] (hS : IsNilpotent (p : S)) (x : M.obj S (ψof S) hS)
    (φ : Spec (CommRingCat.of S) ⟶ H)
    {r : ℕ} (f : Fin r → S) (hspan : Ideal.span (Set.range f) = ⊤)
    (t : ∀ i, Rigidified p Φ (Localization.Away (f i)))
    (ht : ∀ i, (t i).IsAdmissible ι (ψof (Localization.Away (f i))))
    (hn : ∀ i, (t i).n = n)
    (hcont : ∀ i j, ((t i).Φbar (ψof (Localization.Away (f i)))).act ((p : Zp2 p) ^ (n + m)) j ∈ Ideal.span (Set.range (t i).ρ))
    (hηt : ∀ i, haveI : IsNoetherianRing (Localization.Away (f i)) :=
        IsLocalization.isNoetherianRing (Submonoid.powers (f i)) _ inferInstance
      η _ (ψvia S (Localization.Away (f i))) (isNilpotent_p (k := k) _) (t i) =
        M.map hS (isNilpotent_p (k := k) _) (algebraMap S _) rfl x)
    (hφ : ∀ i, haveI : IsNoetherianRing (Localization.Away (f i)) :=
        IsLocalization.isNoetherianRing (Submonoid.powers (f i)) _ inferInstance
      Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (f i)))) ≫ φ =
        (pointOfTriple hΦ4 ι n m pt hmap (t i) (ht i) (hn i) (hcont i)).1) :
    Compat hΦ4 ι n m pt hmap M η S hS φ x := by
  intro g s hs hns hconts hηs
  let L := Localization.Away g
  haveI hLN : IsNoetherianRing L := IsLocalization.isNoetherianRing (Submonoid.powers g) _ inferInstance
  haveI hLiN : ∀ i, IsNoetherianRing (Localization.Away (f i)) := fun i =>
    IsLocalization.isNoetherianRing (Submonoid.powers (f i)) _ inferInstance
  let fL : Fin r → L := fun i => algebraMap S L (f i)
  have hspanL : Ideal.span (Set.range fL) = ⊤ := span_range_algebraMap_eq_top f hspan
  apply glue_opens_unique (fun i => (PrimeSpectrum.basicOpen (fL i) : (Spec (CommRingCat.of L)).Opens))
    (iSup_basicOpen_eq_top fL hspanL)
  intro i
  let L' := Localization.Away (fL i)
  haveI hL'N : IsNoetherianRing L' := IsLocalization.isNoetherianRing (Submonoid.powers (fL i)) _ inferInstance

  let a : L →ₐ[K₀] L' := IsScalarTower.toAlgHom K₀ L L'
  have ha : (a : L →+* L') = algebraMap L L' := rfl
  have hunit : IsUnit ((algebraMap L L').comp (algebraMap S L) (f i)) := IsLocalization.Away.algebraMap_isUnit (fL i)
  let b₀ : Localization.Away (f i) →+* L' := IsLocalization.Away.lift (f i) hunit
  have hb₀ : b₀.comp (algebraMap S (Localization.Away (f i))) = (algebraMap L L').comp (algebraMap S L) :=
    IsLocalization.Away.lift_comp (f i) hunit
  let b : Localization.Away (f i) →ₐ[K₀] L' :=
    { toRingHom := b₀
      commutes' := fun c => by
        show b₀ (algebraMap K₀ (Localization.Away (f i)) c) = algebraMap K₀ L' c
        rw [IsScalarTower.algebraMap_apply K₀ S (Localization.Away (f i)) c, ← RingHom.comp_apply, hb₀,
          IsScalarTower.algebraMap_apply K₀ L L' c, IsScalarTower.algebraMap_apply K₀ S L c]
        rfl }
  have hb : (b : Localization.Away (f i) →+* L') = b₀ := rfl

  have hψa : (a : L →+* L').comp (ψvia S L) = (algebraMap L L').comp (ψvia (p := p) (k := k) S L) := rfl
  have hψb : (b : Localization.Away (f i) →+* L').comp (ψvia S (Localization.Away (f i))) =
      (algebraMap L L').comp (ψvia (p := p) (k := k) S L) := by
    show (b₀.comp (algebraMap S (Localization.Away (f i)))).comp (ψof (p := p) (k := k) S) =
      ((algebraMap L L').comp (algebraMap S L)).comp (ψof (p := p) (k := k) S)
    rw [hb₀]

  have hηa : η L' ((algebraMap L L').comp (ψvia S L)) (isNilpotent_p (k := k) _) (s.map (a : L →+* L')) =
      M.map hS (isNilpotent_p (k := k) _) ((algebraMap L L').comp (algebraMap S L)) rfl x := by
    rw [hη2 _ _ _ _ (isNilpotent_p (k := k) _) (isNilpotent_p (k := k) L') (a : L →+* L') hψa s
      (by rw [ψvia_eq S]; exact hs), hηs, ← M.map_comp]
    exact map_congr M hS (isNilpotent_p (k := k) L') _ _ _ _ (congrArg (fun u => RingHom.comp u (algebraMap S L)) ha) x
  have hηb : η L' ((algebraMap L L').comp (ψvia S L)) (isNilpotent_p (k := k) _) ((t i).map (b : _ →+* L')) =
      M.map hS (isNilpotent_p (k := k) _) ((algebraMap L L').comp (algebraMap S L)) rfl x := by
    rw [hη2 _ _ _ _ (isNilpotent_p (k := k) _) (isNilpotent_p (k := k) L') (b : Localization.Away (f i) →+* L') hψb (t i)
      (by rw [ψvia_eq S]; exact ht i), hηt i, ← M.map_comp]
    exact map_congr M hS (isNilpotent_p (k := k) L') _ _ _ _ hb₀ x
  have hadm_a : (s.map (a : L →+* L')).IsAdmissible ι ((algebraMap L L').comp (ψvia S L)) := by
    rw [← hψa]; exact Rigidified.IsAdmissible.map_ringHom ι _ _ s (by rw [ψvia_eq S]; exact hs)
  have hadm_b : ((t i).map (b : _ →+* L')).IsAdmissible ι ((algebraMap L L').comp (ψvia S L)) := by
    rw [← hψb]; exact Rigidified.IsAdmissible.map_ringHom ι _ _ (t i) (by rw [ψvia_eq S]; exact ht i)
  have hiso : ((t i).map (b : _ →+* L')).IsIsomorphic (s.map (a : L →+* L')) :=
    (hη1 L' _ (isNilpotent_p (k := k) _) _ _ hadm_b hadm_a).mp (hηb.trans hηa.symm)

  have hfac := IsOpenImmersion.isoOfRangeEq_hom_fac (Scheme.Opens.ι (X := Spec (CommRingCat.of L)) (PrimeSpectrum.basicOpen (fL i)))
    (Spec.map (CommRingCat.ofHom (algebraMap L L')))
    (by simp only [Scheme.Opens.range_ι]; exact (PrimeSpectrum.localization_away_comap_range _ _).symm)
  rw [← hfac, Category.assoc, Category.assoc]
  congr 1
  have eb := pointOfTriple_map hΦ4 ι n m pt hmap hnat b (t i) (ht i) (hn i) (hcont i)
    (isAdmissible_map_alg ι b (t i) (ht i)) (hn i) (hcont_map_alg b (t i) (n + m) (hcont i))
  have ea := pointOfTriple_map hΦ4 ι n m pt hmap hnat a s hs hns hconts
    (isAdmissible_map_alg ι a s hs) hns (hcont_map_alg a s (n + m) hconts)
  have step : Spec.map (CommRingCat.ofHom (algebraMap L L')) ≫ Spec.map (CommRingCat.ofHom (algebraMap S L)) =
      Spec.map (CommRingCat.ofHom b₀) ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (f i)))) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hb₀]
  rw [← Category.assoc, step, Category.assoc, hφ i]
  exact eb.symm.trans ((pointOfTriple_congr hΦ4 ι n m pt hmap _ _ _ _ _ _ _ _ hiso).trans ea)

end D4
p2m_reactivate "P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_scheme_nilpPoints_equiv_subtype_act_pow_mem_span_and_isClosedImmersion_toProjSpace.D4.J7 P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_scheme_nilpPoints_equiv_subtype_act_pow_mem_span_and_isClosedImmersion_toProjSpace.D4"

namespace D4

open MvPowerSeries

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p]

local notation "K₀" => (WittVector p k ⧸ pIdeal p (WittVector p k))

theorem exists_Hpoint_of_Mpoint {Φ : FormalODModule p K₀} (hΦ4 : Φ.HasHeight 4) (ι : Zp2 p →+* WittVector p k) (n m : ℕ)
    {H : Scheme.{0}} {q : H ⟶ Spec (CommRingCat.of K₀)}
    (pt : ∀ (S : Type) [CommRing S] [Algebra K₀ S],
      {I : Ideal (MvPowerSeries (Fin 2) S) // PZ K₀ Φ (n + m) (4 * n) S I} ≃
        {g : Spec (CommRingCat.of S) ⟶ H // g ≫ q = Spec.map (CommRingCat.ofHom (algebraMap K₀ S))})
    (hmap : ∀ (S S' : Type) [CommRing S] [CommRing S'] [Algebra K₀ S] [Algebra K₀ S'] (φ : S →ₐ[K₀] S')
      (I : {I : Ideal (MvPowerSeries (Fin 2) S) // PZ K₀ Φ (n + m) (4 * n) S I}),
      PZ K₀ Φ (n + m) (4 * n) S' (I.1.map (MvPowerSeries.map (φ : S →+* S'))))
    (hnat : ∀ (S S' : Type) [CommRing S] [CommRing S'] [Algebra K₀ S] [Algebra K₀ S'] (φ : S →ₐ[K₀] S')
      (I : {I : Ideal (MvPowerSeries (Fin 2) S) // PZ K₀ Φ (n + m) (4 * n) S I}),
      (pt S' ⟨I.1.map (MvPowerSeries.map (φ : S →+* S')), hmap S S' φ I⟩).1 =
        Spec.map (CommRingCat.ofHom (φ : S →+* S')) ≫ (pt S I).1)
    (M : ModuliPackage.{0, 0} p (WittVector p k)) (hM : M.IsZariskiSheaf)
    (η : ∀ (B : Type) [CommRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)), Rigidified p Φ B → M.obj B ψ hB)
    (hη1 : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B))
      (t t' : Rigidified p Φ B), t.IsAdmissible ι ψ → t'.IsAdmissible ι ψ → (η B ψ hB t = η B ψ hB t' ↔ t.IsIsomorphic t'))
    (hη2 : ∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] (ψ : WittVector p k →+* B)
      (ψ' : WittVector p k →+* B') (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (f : B →+* B')
      (hf : f.comp ψ = ψ') (t : Rigidified p Φ B), t.IsAdmissible ι ψ → η B' ψ' hB' (t.map f) = M.map hB hB' f hf (η B ψ hB t))
    (S : Type) [CommRing S] [IsNoetherianRing S] [Algebra K₀ S] (hS : IsNilpotent (p : S)) (x : M.obj S (ψof S) hS)
    (hx : Pnm ι M η n m S hS x) :
    ∃ φ : Spec (CommRingCat.of S) ⟶ H, φ ≫ q = Spec.map (CommRingCat.ofHom (algebraMap K₀ S)) ∧
      Compat hΦ4 ι n m pt hmap M η S hS φ x := by
  classical
  obtain ⟨r, f, hspan, hloc⟩ := hx
  have hLiN : ∀ i, IsNoetherianRing (Localization.Away (f i)) := fun i =>
    IsLocalization.isNoetherianRing (Submonoid.powers (f i)) _ inferInstance
  have hloc' := fun i => hloc i (Localization.Away (f i)) (isNilpotent_p (k := k) _)
  choose t ht using hloc'
  obtain ⟨φ, hφq, hφ⟩ := exists_point_of_cover hΦ4 ι n m pt hmap hnat M η hη1 hη2 S hS x f hspan
    (fun i => isNilpotent_p (k := k) _) t (fun i => (ht i).1) (fun i => (ht i).2.1) (fun i => (ht i).2.2.1)
    (fun i => (ht i).2.2.2)
  refine ⟨φ, hφq, ?_⟩
  have hφ' := fun i => (hφ i)
  choose ht' hcont' hres using hφ'
  exact compat_of_cover hΦ4 ι n m pt hmap hnat M hM η hη1 hη2 S hS x φ f hspan t ht' (fun i => (ht i).2.1) hcont'
    (fun i => (ht i).2.2.2) hres

end D4
p2m_reactivate "P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_scheme_nilpPoints_equiv_subtype_act_pow_mem_span_and_isClosedImmersion_toProjSpace.D4.J7 P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_scheme_nilpPoints_equiv_subtype_act_pow_mem_span_and_isClosedImmersion_toProjSpace.D4"

namespace D4

open MvPowerSeries

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p]

local notation "K₀" => (WittVector p k ⧸ pIdeal p (WittVector p k))

noncomputable def liftAwayAlg {S T : Type} [CommRing S] [Algebra K₀ S] [CommRing T] [Algebra K₀ T] (f : S) (g : S →ₐ[K₀] T)
    (hu : IsUnit (g f)) : Localization.Away f →ₐ[K₀] T :=
  { toRingHom := IsLocalization.Away.lift f (g := (g : S →+* T)) hu
    commutes' := fun c => by
      show IsLocalization.Away.lift f (g := (g : S →+* T)) hu (algebraMap K₀ (Localization.Away f) c) = algebraMap K₀ T c
      rw [IsScalarTower.algebraMap_apply K₀ S (Localization.Away f) c, IsLocalization.Away.lift_eq]
      exact g.commutes c }

theorem liftAwayAlg_comp {S T : Type} [CommRing S] [Algebra K₀ S] [CommRing T] [Algebra K₀ T] (f : S) (g : S →ₐ[K₀] T)
    (hu : IsUnit (g f)) : (liftAwayAlg f g hu : Localization.Away f →+* T).comp (algebraMap S (Localization.Away f)) = (g : S →+* T) :=
  IsLocalization.Away.lift_comp f hu

private theorem _root_.D4.hcont_map_ringHom {Φ : FormalODModule p K₀} {L L' : Type} [CommRing L] [CommRing L'] (ψ : WittVector p k →+* L)
    (c : L →+* L') (t : Rigidified p Φ L) (e : ℕ)
    (hcont : ∀ j, (t.Φbar ψ).act ((p : Zp2 p) ^ e) j ∈ Ideal.span (Set.range t.ρ)) :
    ∀ j, ((t.map c).Φbar (c.comp ψ)).act ((p : Zp2 p) ^ e) j ∈ Ideal.span (Set.range (t.map c).ρ) := by
  intro j
  rw [Rigidified.Φbar_map, Rigidified.map_ρ, FormalODModule.map_act, span_range_map_eq_map]
  exact Ideal.mem_map_of_mem _ (hcont j)

p2m_export "D4" "hcont_map_ringHom"

theorem pnm_compat_map {Φ : FormalODModule p K₀} (hΦ4 : Φ.HasHeight 4) (ι : Zp2 p →+* WittVector p k) (n m : ℕ)
    {H : Scheme.{0}} {q : H ⟶ Spec (CommRingCat.of K₀)}
    (pt : ∀ (S : Type) [CommRing S] [Algebra K₀ S],
      {I : Ideal (MvPowerSeries (Fin 2) S) // PZ K₀ Φ (n + m) (4 * n) S I} ≃
        {g : Spec (CommRingCat.of S) ⟶ H // g ≫ q = Spec.map (CommRingCat.ofHom (algebraMap K₀ S))})
    (hmap : ∀ (S S' : Type) [CommRing S] [CommRing S'] [Algebra K₀ S] [Algebra K₀ S'] (φ : S →ₐ[K₀] S')
      (I : {I : Ideal (MvPowerSeries (Fin 2) S) // PZ K₀ Φ (n + m) (4 * n) S I}),
      PZ K₀ Φ (n + m) (4 * n) S' (I.1.map (MvPowerSeries.map (φ : S →+* S'))))
    (hnat : ∀ (S S' : Type) [CommRing S] [CommRing S'] [Algebra K₀ S] [Algebra K₀ S'] (φ : S →ₐ[K₀] S')
      (I : {I : Ideal (MvPowerSeries (Fin 2) S) // PZ K₀ Φ (n + m) (4 * n) S I}),
      (pt S' ⟨I.1.map (MvPowerSeries.map (φ : S →+* S')), hmap S S' φ I⟩).1 =
        Spec.map (CommRingCat.ofHom (φ : S →+* S')) ≫ (pt S I).1)
    (M : ModuliPackage.{0, 0} p (WittVector p k)) (hM : M.IsZariskiSheaf)
    (η : ∀ (B : Type) [CommRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)), Rigidified p Φ B → M.obj B ψ hB)
    (hη1 : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B))
      (t t' : Rigidified p Φ B), t.IsAdmissible ι ψ → t'.IsAdmissible ι ψ → (η B ψ hB t = η B ψ hB t' ↔ t.IsIsomorphic t'))
    (hη2 : ∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] (ψ : WittVector p k →+* B)
      (ψ' : WittVector p k →+* B') (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (f : B →+* B')
      (hf : f.comp ψ = ψ') (t : Rigidified p Φ B), t.IsAdmissible ι ψ → η B' ψ' hB' (t.map f) = M.map hB hB' f hf (η B ψ hB t))
    (S S' : Type) [CommRing S] [CommRing S'] [IsNoetherianRing S] [IsNoetherianRing S'] [Algebra K₀ S] [Algebra K₀ S']
    (hS : IsNilpotent (p : S)) (hS' : IsNilpotent (p : S')) (g : S →ₐ[K₀] S') (x : M.obj S (ψof S) hS)
    (φ : Spec (CommRingCat.of S) ⟶ H) (hx : Pnm ι M η n m S hS x) (hφ : Compat hΦ4 ι n m pt hmap M η S hS φ x)
    (hg : (g : S →+* S').comp (ψof S) = ψof S') :
    Pnm ι M η n m S' hS' (M.map hS hS' (g : S →+* S') hg x) ∧
    Compat hΦ4 ι n m pt hmap M η S' hS' (Spec.map (CommRingCat.ofHom (g : S →+* S')) ≫ φ) (M.map hS hS' (g : S →+* S') hg x) := by
  classical
  obtain ⟨r, f, hspan, hloc⟩ := hx
  have hLiN : ∀ i, IsNoetherianRing (Localization.Away (f i)) := fun i =>
    IsLocalization.isNoetherianRing (Submonoid.powers (f i)) _ inferInstance
  have hloc' := fun i => hloc i (Localization.Away (f i)) (isNilpotent_p (k := k) _)
  choose t ht using hloc'
  let f' : Fin r → S' := fun i => g (f i)
  have hspan' : Ideal.span (Set.range f') = ⊤ := by
    have := congrArg (Ideal.map (g : S →+* S')) hspan
    rwa [Ideal.map_top, ideal_map_span_range] at this

  have transport : ∀ (i : Fin r) (L' : Type) [CommRing L'] [IsNoetherianRing L'] [Algebra S' L'] [IsLocalization.Away (f' i) L']
      (hL' : IsNilpotent (p : L')),
      ∃ (c : Localization.Away (f i) →+* L') (hc : c.comp (algebraMap S (Localization.Away (f i))) = (algebraMap S' L').comp (g : S →+* S')),
        ((t i).map c).IsAdmissible ι (ψvia S' L') ∧ ((t i).map c).n = n ∧
        (∀ j, (((t i).map c).Φbar (ψvia S' L')).act ((p : Zp2 p) ^ (n + m)) j ∈ Ideal.span (Set.range ((t i).map c).ρ)) ∧
        η L' (ψvia S' L') hL' ((t i).map c) = M.map hS' hL' (algebraMap S' L') rfl (M.map hS hS' (g : S →+* S') hg x) := by
    intro i L' _ _ _ _ hL'
    have hu : IsUnit (((algebraMap S' L').comp (g : S →+* S')) (f i)) := IsLocalization.Away.algebraMap_isUnit (f' i)
    let c : Localization.Away (f i) →+* L' := IsLocalization.Away.lift (f i) hu
    have hc : c.comp (algebraMap S (Localization.Away (f i))) = (algebraMap S' L').comp (g : S →+* S') :=
      IsLocalization.Away.lift_comp (f i) hu
    have hψ : c.comp (ψvia S (Localization.Away (f i))) = ψvia (p := p) (k := k) S' L' := by
      show (c.comp (algebraMap S (Localization.Away (f i)))).comp (ψof (p := p) (k := k) S) = (algebraMap S' L').comp (ψof (p := p) (k := k) S')
      rw [hc, RingHom.comp_assoc, hg]
    refine ⟨c, hc, ?_, (ht i).2.1, ?_, ?_⟩
    · rw [← hψ]; exact Rigidified.IsAdmissible.map_ringHom ι _ c (t i) (ht i).1
    · rw [← hψ]; exact hcont_map_ringHom _ c (t i) (n + m) (ht i).2.2.1
    · rw [hη2 _ _ _ _ (isNilpotent_p (k := k) _) hL' c hψ (t i) (ht i).1, (ht i).2.2.2, ← M.map_comp, ← M.map_comp]
      exact map_congr M hS hL' _ _ _ _ hc x
  refine ⟨⟨r, f', hspan', fun i L' _ _ _ _ hL' => ?_⟩, ?_⟩
  · obtain ⟨c, hc, h1, h2, h3, h4⟩ := transport i L' hL'
    exact ⟨(t i).map c, h1, h2, h3, h4⟩
  ·
    have hL'N : ∀ i, IsNoetherianRing (Localization.Away (f' i)) := fun i =>
      IsLocalization.isNoetherianRing (Submonoid.powers (f' i)) _ inferInstance
    have data := fun i => transport i (Localization.Away (f' i)) (isNilpotent_p (k := k) _)
    choose c hc h1 h2 h3 h4 using data
    have h1' : ∀ i, ((t i).map (c i)).IsAdmissible ι (ψof (Localization.Away (f' i))) := fun i => by
      rw [← ψvia_eq S']; exact h1 i
    have h3' : ∀ i j, (((t i).map (c i)).Φbar (ψof (Localization.Away (f' i)))).act ((p : Zp2 p) ^ (n + m)) j ∈
        Ideal.span (Set.range ((t i).map (c i)).ρ) := fun i => by rw [← ψvia_eq S']; exact h3 i
    refine compat_of_cover hΦ4 ι n m pt hmap hnat M hM η hη1 hη2 S' hS' _ _ f' hspan' (fun i => (t i).map (c i)) h1' h2 h3' h4 ?_
    intro i

    let cA : Localization.Away (f i) →ₐ[K₀] Localization.Away (f' i) :=
      { toRingHom := c i
        commutes' := fun a => by
          show c i (algebraMap K₀ (Localization.Away (f i)) a) = algebraMap K₀ (Localization.Away (f' i)) a
          rw [IsScalarTower.algebraMap_apply K₀ S (Localization.Away (f i)) a, ← RingHom.comp_apply, hc i, RingHom.comp_apply,
            IsScalarTower.algebraMap_apply K₀ S' (Localization.Away (f' i)) a]
          exact congrArg _ (g.commutes a) }
    have hcA : (cA : Localization.Away (f i) →+* Localization.Away (f' i)) = c i := rfl
    have htv : (t i).IsAdmissible ι (ψof (Localization.Away (f i))) := by rw [← ψvia_eq S]; exact (ht i).1
    have hcv : ∀ j, ((t i).Φbar (ψof (Localization.Away (f i)))).act ((p : Zp2 p) ^ (n + m)) j ∈ Ideal.span (Set.range (t i).ρ) := by
      rw [← ψvia_eq S]; exact (ht i).2.2.1
    have e0 := hφ (f i) (t i) htv (ht i).2.1 hcv (ht i).2.2.2
    have e1 := pointOfTriple_map hΦ4 ι n m pt hmap hnat cA (t i) htv (ht i).2.1 hcv (h1' i) (h2 i) (h3' i)
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← hc i, CommRingCat.ofHom_comp, Spec.map_comp,
      Category.assoc, e0]
    exact e1.symm

end D4
p2m_reactivate "P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_scheme_nilpPoints_equiv_subtype_act_pow_mem_span_and_isClosedImmersion_toProjSpace.D4.J7 P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_scheme_nilpPoints_equiv_subtype_act_pow_mem_span_and_isClosedImmersion_toProjSpace.D4"

namespace D4

open MvPowerSeries

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p]

local notation "K₀" => (WittVector p k ⧸ pIdeal p (WittVector p k))

theorem specialAt_kerIdeal {Φ : FormalODModule p K₀} (hΦ4 : Φ.HasHeight 4) (ι : Zp2 p →+* WittVector p k) {L : Type} [CommRing L]
    [IsNoetherianRing L] [Algebra K₀ L] (t : Rigidified p Φ L) (ht : t.IsAdmissible ι (ψof L)) :
    SpecialAt Φ ι L (kerIdeal t) := by
  let s : (L ⧸ pIdeal p L) →+* L := (quotAlgEquiv (p := p) (k := k) L).symm.toRingEquiv.toRingHom
  have hms : s.comp (Ideal.Quotient.mk (pIdeal p L)) = RingHom.id _ := by
    ext y; exact (quotAlgEquiv (p := p) (k := k) L).symm_apply_apply y
  have hsψ : s.comp (residueMap (ψof L)) = algebraMap K₀ L := by
    rw [← algebraMap_quot_eq_residueMap]
    ext c
    show s (Ideal.Quotient.mk (pIdeal p L) (algebraMap K₀ L c)) = algebraMap K₀ L c
    exact (quotAlgEquiv (p := p) (k := k) L).symm_apply_apply _
  have hX : t.Xbar.map s = t.X := by
    show (t.X.map (Ideal.Quotient.mk (pIdeal p L))).map s = t.X
    rw [FormalODModule.map_map, hms, FormalODModule.map_id]
  have hρ : FormalODModule.IsODHom (Φ.map (algebraMap K₀ L)) t.X (t.ρ.map s) := by
    have h := ht.2.2.1.map s
    rwa [hX, show (t.Φbar (ψof L)).map s = Φ.map (algebraMap K₀ L) from by
      show (Φ.map (residueMap (ψof L))).map s = _; rw [FormalODModule.map_map, hsψ]] at h
  have hker : FormalODModule.HasKernelOfDegree (t.ρ.map s) (p ^ (4 * t.n)) :=
    CerednikDrinfeld.FormalODModule.hasKernelOfDegree_map s t.ρ ht.2.2.1.constantCoeff ht.2.2.2
  exact specialAt_of_presentation ι (kerIdeal t) t.X (t.ρ.map s) hρ hker (span_range_map_eq_map s t.ρ) ht.1

end D4
p2m_reactivate "P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_scheme_nilpPoints_equiv_subtype_act_pow_mem_span_and_isClosedImmersion_toProjSpace.D4.J7 P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_scheme_nilpPoints_equiv_subtype_act_pow_mem_span_and_isClosedImmersion_toProjSpace.D4"

open D4 in
theorem solution
(p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
(ι : Zp2 p →+* WittVector p k)
(Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
(hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι))
(hΦ4 : Φ.HasHeight 4)
(h0Φ : Φ.lieZero ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) ≤ LinearMap.ker Φ.lieVarpi)
(M : ModuliPackage.{0, 0} p (WittVector p k)) (hM : M.IsZariskiSheaf)
(η : ∀ (B : Type) [CommRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)),
Rigidified p Φ B → M.obj B ψ hB)
(hη : (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B))
(t t' : Rigidified p Φ B), t.IsAdmissible ι ψ → t'.IsAdmissible ι ψ →
(η B ψ hB t = η B ψ hB t' ↔ t.IsIsomorphic t')) ∧
(∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] (ψ : WittVector p k →+* B) (ψ' : WittVector p k →+* B')
(hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (f : B →+* B')
(hf : f.comp ψ = ψ') (t : Rigidified p Φ B), t.IsAdmissible ι ψ →
η B' ψ' hB' (t.map f) = M.map hB hB' f hf (η B ψ hB t)) ∧
(∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)) (m : M.obj B ψ hB),
∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
∀ (i : Fin n) (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra B L] [IsLocalization.Away (f i) L]
(hL : IsNilpotent (p : L)),
∃ t : Rigidified p Φ L, t.IsAdmissible ι ((algebraMap B L).comp ψ) ∧
η L ((algebraMap B L).comp ψ) hL t =
M.map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl m))
(n m : ℕ)
    :
    ∃ (X : Scheme.{0}) (fX : X ⟶ Spec (CommRingCat.of (WittVector p k ⧸ pIdeal p (WittVector p k))))
      (e : ∀ (S : Type) [CommRing S] [IsNoetherianRing S] [Algebra (WittVector p k ⧸ pIdeal p (WittVector p k)) S] (hS : IsNilpotent (p : S)),
        (Scheme.nilpPoints fX).obj S ≃
          {x : M.obj S ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) S).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) hS //
            ∃ (r : ℕ) (f : Fin r → S), Ideal.span (Set.range f) = ⊤ ∧
            ∀ (i : Fin r) (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra S L] [IsLocalization.Away (f i) L]
              (hL : IsNilpotent (p : L)),
              ∃ t : Rigidified p Φ L, t.IsAdmissible ι ((algebraMap S L).comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) S).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) ∧ t.n = n ∧
                (∀ j : Fin 2, (t.Φbar ((algebraMap S L).comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) S).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))))).act ((p : Zp2 p) ^ (n + m)) j ∈ Ideal.span (Set.range t.ρ)) ∧
                η L ((algebraMap S L).comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) S).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) hL t =
                  M.map (ψ' := (algebraMap S L).comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) S).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) hS hL (algebraMap S L) rfl x}),
      (∀ (S S' : Type) [CommRing S] [CommRing S'] [IsNoetherianRing S] [IsNoetherianRing S'] [Algebra (WittVector p k ⧸ pIdeal p (WittVector p k)) S] [Algebra (WittVector p k ⧸ pIdeal p (WittVector p k)) S']
        (hS : IsNilpotent (p : S)) (hS' : IsNilpotent (p : S')) (g : S →ₐ[(WittVector p k ⧸ pIdeal p (WittVector p k))] S')
        (x : (Scheme.nilpPoints fX).obj S),
        ((e S' hS' ((Scheme.nilpPoints fX).map g x)) : M.obj S' ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) S').comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) hS') =
          M.map hS hS' (g : S →+* S') (by rw [← RingHom.comp_assoc, AlgHom.comp_algebraMap]) (e S hS x : M.obj S ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) S).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) hS)) ∧
      ∃ (mP : ℕ) (ιP : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (mP + 1)) (WittVector p k ⧸ pIdeal p (WittVector p k)))),
        IsClosedImmersion ιP ∧ ιP ≫ ProjSpace.π (WittVector p k ⧸ pIdeal p (WittVector p k)) mP = fX := by
  classical

  obtain ⟨hfin, hfree, hX⟩ := D4.kerAlgebra_inputs' Φ hΦ4 (n + m)
  haveI := hfin
  haveI := hfree
  obtain ⟨H, q, pt, hmap, hnat, mP, ιP, hιP, hcomp⟩ :=
    CerednikDrinfeld.FormalODModule.exists_scheme_represents_subgroup_ideal_and_isClosedImmersion_toProjSpace p
      (WittVector p k ⧸ pIdeal p (WittVector p k)) Φ (n + m) (4 * n) hX
  haveI := hιP
  have hq : LocallyOfFiniteType q := by rw [← hcomp]; infer_instance

  obtain ⟨X, ιX, hop, hcl, hXpt⟩ := D4.special_locus hΦ4 ι n m hq pt hmap hnat
  haveI := hop
  haveI := hcl

  have toM : ∀ (S : Type) [CommRing S] [IsNoetherianRing S] [Algebra (WittVector p k ⧸ pIdeal p (WittVector p k)) S] (hS : IsNilpotent (p : S))
      (φX : (Scheme.nilpPoints (ιX ≫ q)).obj S),
      ∃ x : M.obj S (ψof S) hS, Pnm ι M η n m S hS x ∧ Compat hΦ4 ι n m pt hmap M η S hS (φX.1 ≫ ιX) x := by
    intro S _ _ _ hS φX
    have hφ : (φX.1 ≫ ιX) ≫ q = Spec.map (CommRingCat.ofHom (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) S)) := by
      rw [Category.assoc]; exact φX.2
    refine exists_Mpoint_of_Hpoint hΦ4 ι n m pt hmap hnat M hM η hη.1 hη.2.1 S hS (φX.1 ≫ ιX) hφ ?_
    exact (hXpt S _).mpr ⟨φX.1, by rw [Equiv.apply_symm_apply]⟩

  have toH : ∀ (S : Type) [CommRing S] [IsNoetherianRing S] [Algebra (WittVector p k ⧸ pIdeal p (WittVector p k)) S] (hS : IsNilpotent (p : S))
      (x : M.obj S (ψof S) hS), Pnm ι M η n m S hS x →
      ∃ φX : (Scheme.nilpPoints (ιX ≫ q)).obj S, Compat hΦ4 ι n m pt hmap M η S hS (φX.1 ≫ ιX) x := by
    intro S _ _ _ hS x hx
    obtain ⟨φ, hφq, hφ⟩ := exists_Hpoint_of_Mpoint hΦ4 ι n m pt hmap hnat M hM η hη.1 hη.2.1 S hS x hx

    have hrange : Set.range φ.base ⊆ Set.range ιX.base := by
      obtain ⟨r, f, hspan, hloc⟩ := hx
      rintro _ ⟨s, rfl⟩
      have hcov : s ∈ (⨆ i, PrimeSpectrum.basicOpen (f i) : (Spec (CommRingCat.of S)).Opens) := by
        rw [iSup_basicOpen_eq_top f hspan]; trivial
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hcov
      haveI : IsNoetherianRing (Localization.Away (f i)) :=
        IsLocalization.isNoetherianRing (Submonoid.powers (f i)) _ inferInstance
      obtain ⟨t, ht, hn, hcont, hηt⟩ := hloc i (Localization.Away (f i)) (isNilpotent_p (k := k) _)
      have ht' : t.IsAdmissible ι (ψof (Localization.Away (f i))) := by rw [← ψvia_eq S]; exact ht
      have hcont' : ∀ j, (t.Φbar (ψof (Localization.Away (f i)))).act ((p : Zp2 p) ^ (n + m)) j ∈ Ideal.span (Set.range t.ρ) := by
        rw [← ψvia_eq S]; exact hcont
      have e1 := hφ (f i) t ht' hn hcont' hηt

      obtain ⟨g, hg⟩ := (hXpt (Localization.Away (f i)) ⟨kerIdeal t, hmap _ _ (quotAlgEquiv (k := k) (Localization.Away (f i))).symm.toAlgHom
        ⟨Ideal.span (Set.range t.ρ), PZ_quot_of_isAdmissible hΦ4 ι t ht' n m hn hcont'⟩⟩).mp (specialAt_kerIdeal hΦ4 ι t ht')

      have hs' : s ∈ Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away (f i)))) := by
        rw [PrimeSpectrum.localization_away_comap_range (Localization.Away (f i)) (f i)]; exact hi
      obtain ⟨u, hu⟩ := hs'
      subst hu
      refine ⟨g.base u, ?_⟩
      change (g ≫ ιX).base u = (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (f i)))) ≫ φ).base u
      rw [hg, e1]
      rfl
    refine ⟨⟨IsOpenImmersion.lift ιX φ hrange, ?_⟩, ?_⟩
    · show IsOpenImmersion.lift ιX φ hrange ≫ ιX ≫ q = _
      rw [← Category.assoc, IsOpenImmersion.lift_fac, hφq]
    · show Compat hΦ4 ι n m pt hmap M η S hS (IsOpenImmersion.lift ιX φ hrange ≫ ιX) x
      rw [IsOpenImmersion.lift_fac]; exact hφ

  let toFun : ∀ (S : Type) [CommRing S] [IsNoetherianRing S] [Algebra (WittVector p k ⧸ pIdeal p (WittVector p k)) S] (hS : IsNilpotent (p : S)),
      (Scheme.nilpPoints (ιX ≫ q)).obj S → {x : M.obj S (ψof S) hS // Pnm ι M η n m S hS x} :=
    fun S _ _ _ hS φX => ⟨Classical.choose (toM S hS φX), (Classical.choose_spec (toM S hS φX)).1⟩
  have toFun_compat : ∀ (S : Type) [CommRing S] [IsNoetherianRing S] [Algebra (WittVector p k ⧸ pIdeal p (WittVector p k)) S] (hS : IsNilpotent (p : S))
      (φX : (Scheme.nilpPoints (ιX ≫ q)).obj S), Compat hΦ4 ι n m pt hmap M η S hS (φX.1 ≫ ιX) (toFun S hS φX).1 :=
    fun S _ _ _ hS φX => (Classical.choose_spec (toM S hS φX)).2
  have hbij : ∀ (S : Type) [CommRing S] [IsNoetherianRing S] [Algebra (WittVector p k ⧸ pIdeal p (WittVector p k)) S] (hS : IsNilpotent (p : S)),
      Function.Bijective (toFun S hS) := by
    intro S _ _ _ hS
    constructor
    · intro φ₁ φ₂ h
      have c1 := toFun_compat S hS φ₁
      have c2 := toFun_compat S hS φ₂
      rw [h] at c1
      have := Compat.unique_point hΦ4 ι n m pt hmap M η S hS _ _ _ c1 c2 (toFun S hS φ₂).2
      apply Subtype.ext
      exact (cancel_mono ιX).mp this
    · rintro ⟨x, hx⟩
      obtain ⟨φX, hφX⟩ := toH S hS x hx
      refine ⟨φX, Subtype.ext ?_⟩
      exact Compat.unique_M hΦ4 ι n m pt hmap hnat M hM η hη.1 hη.2.1 S hS _ _ _ (toFun_compat S hS φX) hφX
        (toFun S hS φX).2 hx
  refine ⟨X, ιX ≫ q, fun S _ _ _ hS => Equiv.ofBijective (toFun S hS) (hbij S hS), ?_, mP, ιX ≫ ιP, inferInstance,
    by rw [Category.assoc, hcomp]⟩

  intro S S' _ _ _ _ _ _ hS hS' g φX
  show (toFun S' hS' ((Scheme.nilpPoints (ιX ≫ q)).map g φX)).1 = M.map hS hS' (g : S →+* S') _ (toFun S hS φX).1
  have c' := toFun_compat S' hS' ((Scheme.nilpPoints (ιX ≫ q)).map g φX)
  have hg : (g : S →+* S').comp (ψof S) = ψof S' := algHom_comp_ψof g
  obtain ⟨hP, c⟩ := pnm_compat_map hΦ4 ι n m pt hmap hnat M hM η hη.1 hη.2.1 S S' hS hS' g (toFun S hS φX).1 (φX.1 ≫ ιX)
    (toFun S hS φX).2 (toFun_compat S hS φX) hg
  have hval : ((Scheme.nilpPoints (ιX ≫ q)).map g φX).1 ≫ ιX = Spec.map (CommRingCat.ofHom (g : S →+* S')) ≫ φX.1 ≫ ιX := by
    rw [Scheme.nilpPoints_map_val, Category.assoc]; rfl
  rw [hval] at c'
  exact Compat.unique_M hΦ4 ι n m pt hmap hnat M hM η hη.1 hη.2.1 S' hS' _ _ _ c' c
    (toFun S' hS' ((Scheme.nilpPoints (ιX ≫ q)).map g φX)).2 hP

end S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_scheme_nilpPoints_equiv_subtype_act_pow_mem_span_and_isClosedImmersion_toProjSpace
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_scheme_nilpPoints_equiv_subtype_act_pow_mem_span_and_isClosedImmersion_toProjSpace (solution)
