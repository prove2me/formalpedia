-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_rigidifiedCurve_isRigTransport_zero_isIsomorphic_of_quotient_of_isFormalModuleVia
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/74ac86f6-6c87-5eb3-b1a8-8c3e0e9d379f

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime

import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullback_levelIff
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_IsPullbackVia_comp
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isIsogenyPair_comp_eq_of_isPullbackVia_of_isPullbackVia
import Theorems.Thm_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_comp
import Theorems.Thm_CerednikDrinfeld_FormalODModule_HasHeight_hasKernelOfDegree_act_pow
import Theorems.Thm_CerednikDrinfeld_FormalODModule_hasKernelOfDegree_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_rigidifiedCurve_isRigTransport_zero_isIsomorphic_of_quotient_of_isFormalModuleVia
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.FormalOmega CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

namespace RQasm

theorem isIsogenyPair_symm {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S] (d : ℕ)
    (E E' : FakeEllipticCurve Λ N S) (φ : E.A ⟶ E'.A) (ψ : E'.A ⟶ E.A) (h : FakeEllipticCurve.IsIsogenyPair d E E' φ ψ) :
    FakeEllipticCurve.IsIsogenyPair d E' E ψ φ := by
  obtain ⟨hφ, hψ, h1, h2, h3, h4, h5⟩ := h
  exact ⟨hψ, hφ, h2, h1, h4, h3, fun hd => ⟨(h5 hd).2, (h5 hd).1⟩⟩

theorem isIsogenyOfHeight_act_pow_comp {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] [IsNoetherianRing B]
    (Φ X : FormalODModule p B)
    (ρ : Series B) (n e : ℕ) (hX : X.HasHeight 4) (hρ : FormalODModule.IsIsogenyOfHeight Φ X ρ (4 * n)) :
    FormalODModule.IsIsogenyOfHeight Φ X ((X.act ((p : Zp2 p) ^ e)).comp ρ) (4 * (n + e)) := by
  refine ⟨(FormalODModule.IsODHom.act_natCast_pow X e).comp hρ.1, ?_⟩
  have hk := CerednikDrinfeld.FormalODModule.HasKernelOfDegree.comp hρ.1.constantCoeff (X.isLawHom_act _).1 hρ.2
    (CerednikDrinfeld.FormalODModule.HasHeight.hasKernelOfDegree_act_pow hX e)
  rw [← pow_add, show 4 * n + 4 * e = 4 * (n + e) by ring] at hk
  exact hk

theorem preservesLevel_of_isPullbackVia
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S S' : Type} [CommRing S] [CommRing S'] (f : S →+* S')
    (E A : FakeEllipticCurve Λ N S) (Eb Ab : FakeEllipticCurve Λ N S')
    (gb : Eb.A ⟶ E.A) (hgb : FakeEllipticCurve.IsPullbackVia f E Eb gb)
    (uA : Ab.A ⟶ A.A) (huAf : uA ≫ A.f = Ab.f ≫ Spec.map (CommRingCat.ofHom f))
    (huA_lev' : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' Ab.f),
      (∃ P₀ : T ⟶ A.C, P₀ ≫ A.lev = P.1 ≫ uA) → FactorsThrough Ab.lev P)
    (p' : E.A ⟶ A.A) (hp' : p' ≫ A.f = E.f) (hlev : FakeEllipticCurve.PreservesLevel E A p' hp')
    (φ : Eb.A ⟶ Ab.A) (hφ : φ ≫ uA = gb ≫ p') (hφf : φ ≫ Ab.f = Eb.f) :
    FakeEllipticCurve.PreservesLevel Eb Ab φ hφf := by
  intro T t' P hP
  obtain ⟨hsq, -, -, hglev⟩ := hgb
  obtain ⟨P₀, hP₀⟩ := hglev t' P hP
  have hPg : (P.1 ≫ gb) ≫ E.f = t' ≫ Spec.map (CommRingCat.ofHom f) := by
    rw [Category.assoc, hsq.w, ← Category.assoc, P.2]
  have hfac : FactorsThrough E.lev
      (⟨P.1 ≫ gb, hPg⟩ : SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom f)) E.f) := ⟨P₀, hP₀⟩
  obtain ⟨Q₀, hQ₀⟩ := hlev (t' ≫ Spec.map (CommRingCat.ofHom f)) ⟨P.1 ≫ gb, hPg⟩ hfac
  apply huA_lev' t' (mapPt φ hφf P)
  refine ⟨Q₀, ?_⟩
  rw [hQ₀, mapPt_coe, mapPt_coe, Category.assoc, Category.assoc, hφ]

theorem hasHeight_map {p : ℕ} [Fact p.Prime] {B B' : Type} [CommRing B] [IsNoetherianRing B] [CommRing B']
    (f : B →+* B') (X : FormalODModule p B) (h : ℕ) (hX : X.HasHeight h) : (X.map f).HasHeight h :=
  CerednikDrinfeld.FormalODModule.hasKernelOfDegree_map f (X.act (p : Zp2 p)) (X.isLawHom_act _).1 hX

theorem nilEval_map_of_algebraMap_eq {R S B'' : Type} [CommRing R] [CommRing S] [CommRing B''] [Algebra R B''] [Algebra S B'']
    (ψ : R →+* S) (h : algebraMap R B'' = (algebraMap S B'').comp ψ) {σ : Type} [Fintype σ] [DecidableEq σ]
    (n : ℕ) (φ : MvPowerSeries σ R) (a : σ → B'') :
    MvFormalGroup.nilEval n (MvPowerSeries.map ψ φ) a = MvFormalGroup.nilEval n φ a := by
  unfold MvFormalGroup.nilEval
  have htr : MvPowerSeries.trunc' S (Finsupp.equivFunOnFinite.symm fun _ => n) (MvPowerSeries.map ψ φ) =
      MvPolynomial.map ψ (MvPowerSeries.trunc' R (Finsupp.equivFunOnFinite.symm fun _ => n) φ) := by
    ext m
    rw [MvPowerSeries.coeff_trunc', MvPolynomial.coeff_map, MvPowerSeries.coeff_trunc']
    split_ifs with hm
    · exact MvPowerSeries.coeff_map _ _ _
    · exact (map_zero ψ).symm
  rw [htr, MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_map, ← h]

end RQasm

set_option maxHeartbeats 3200000 in
theorem solution
    {r rbar N : ℕ} [Fact r.Prime] [Fact rbar.Prime] [NeZero N] (hrr : rbar ≠ r) (hrN : ¬ r ∣ N)

    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (K₀ : Type) [Field K₀] [CharZero K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]

    (Onr : Type) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π})

    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b r rbar)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (X₀ : FormalODModule r (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})) (hX₀ : X₀.HasHeight 4)
    (θ₀ : RelativeGroupLaw.FormalCoordinates A₀.f 2) (hA₀ : A₀.IsFormalModuleVia coord X₀ θ₀)

    (ι : Zp2 r →+* Onr)
    (Φ : FormalODModule r (Onr ⧸ pIdeal r Onr))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal r Onr)).comp ι))
    (hΦ4 : Φ.HasHeight 4)
    (E₀ : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) K₀)
    (hE₀ : Function.Injective E₀ ∧
      ∃ m : ℕ,
        (∀ A : Matrix (Fin 2) (Fin 2) 𝒪, ∃ e, E₀ e = (r : K₀) ^ m • A.map (algebraMap 𝒪 K₀)) ∧
        (∀ e, ∃ A : Matrix (Fin 2) (Fin 2) 𝒪, (r : K₀) ^ m • E₀ e = A.map (algebraMap 𝒪 K₀)))

    (κ : (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) →+* (Onr ⧸ pIdeal r Onr))
    (hκ : κ.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 Onr π})) = Ideal.Quotient.mk (pIdeal r Onr))
    (n₀ : ℕ) (β₀ : Series (Onr ⧸ pIdeal r Onr)) (hβ₀ : FormalODModule.IsIsogenyOfHeight Φ (X₀.map κ) β₀ (4 * n₀))

    (k : Type) [Field k] [IsAlgClosed k] [Algebra 𝒪 k] (hk : IsNilpotent (algebraMap 𝒪 k π)) (hkr : IsNilpotent ((r : ℕ) : k))
    (ψ : Onr →ₐ[𝒪] k) (t : Rigidified r Φ k) (ht : t.IsAdmissible ι ((ψ : Onr →ₐ[𝒪] k) : Onr →+* k))

    (ψb : (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) →+* k)
    (hψb : ψb.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 Onr π})) = ((ψ : Onr →ₐ[𝒪] k) : Onr →+* k))
    (A : FakeEllipticCurve Λ N k) (gA₀ : A.A ⟶ A₀.A) (hA : FakeEllipticCurve.IsPullbackVia ψb A₀ A gA₀)
    (θA : RelativeGroupLaw.FormalCoordinates A.f 2) (hXA : A.IsFormalModuleVia coord (X₀.map ψb) θA)
    (hθA : ∀ (B'' : Type) [CommRing B''] [Algebra k B''] [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B''],
      algebraMap (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'' = (algebraMap k B'').comp ψb →
      ∀ s : Fin 2 → B'', (∀ i, IsNilpotent (s i)) → (θA B'' s).1 ≫ gA₀ = (θ₀ B'' s).1)

    (E : FakeEllipticCurve Λ N k) (p : A.A ⟶ E.A) (hp : p ≫ E.f = A.f) (p' : E.A ⟶ A.A) (hp' : p' ≫ A.f = E.f)
    (c : ℕ) (hpair : FakeEllipticCurve.IsIsogenyPair (r ^ c) A E p p')
    (hlev : FakeEllipticCurve.PreservesLevel E A p' hp')

    (θE : RelativeGroupLaw.FormalCoordinates E.f 2) (hXE : E.IsFormalModuleVia coord t.X θE)
    (γp : Series k) (hγp : FormalODModule.IsODHom (X₀.map ψb) t.X γp)
    (hγp_germ : ∀ (B'' : Type) [CommRing B''] [Algebra k B''] (J : Ideal B'') (n : ℕ), J ^ (n + 1) = ⊥ →
      ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
        (θA B'' s).1 ≫ p = (θE B'' (fun i => MvFormalGroup.nilEval n (γp i) s)).1)
    (e : ℕ)
    (hγρ : (γp.map (Ideal.Quotient.mk (pIdeal r k))).comp (β₀.map (residueMap ((ψ : Onr →ₐ[𝒪] k) : Onr →+* k))) =
      (t.Xbar.act ((r : Zp2 r) ^ e)).comp t.ρ) :
    ∃ (x : FakeEllipticCurve.RigidifiedCurve r π A₀ k ψ) (X : FormalODModule r k) (θ : RelativeGroupLaw.FormalCoordinates x.1.f 2)
      (t' : Rigidified r Φ k),
      x.1.IsFormalModuleVia coord X θ ∧ t'.X = X ∧
      FakeEllipticCurve.Rigidification.IsRigTransport θ₀ κ β₀ x.2 θ 0 t' ∧
      t'.IsAdmissible ι ((ψ : Onr →ₐ[𝒪] k) : Onr →+* k) ∧ t'.IsIsomorphic t := by
  classical
  have hrp : r.Prime := Fact.out
  have hπ0 : algebraMap 𝒪 k π = 0 := hk.eq_zero

  obtain ⟨Eb, gb, hgb_sq, hgb_mul, hgb_act, hgb_lev, hgb_lev'⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_levelIff (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 k π})) E
  have hgb : FakeEllipticCurve.IsPullbackVia (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 k π})) E Eb gb := ⟨hgb_sq, hgb_mul, hgb_act, hgb_lev⟩
  obtain ⟨Ab, uA, huA_sq, huA_mul, huA_act, huA_lev, huA_lev'⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_levelIff (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 k π})) A
  have huA : FakeEllipticCurve.IsPullbackVia (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 k π})) A Ab uA := ⟨huA_sq, huA_mul, huA_act, huA_lev⟩

  have hleg : FakeEllipticCurve.Rigidification.residueLeg π ψ = ((Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 k π}))).comp ψb := by
    apply Ideal.Quotient.ringHom_ext
    rw [RingHom.comp_assoc, hψb]
    exact Ideal.quotientMap_comp_mk _
  have hAbA₀ : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π ψ) A₀ Ab (uA ≫ gA₀) := by
    rw [hleg]
    exact CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia.comp ψb (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 k π})) A₀ A Ab gA₀ uA hA huA

  obtain ⟨φ, φ', hφuA, hφ'gb, hpairb⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_isIsogenyPair_comp_eq_of_isPullbackVia_of_isPullbackVia
      p' p (RQasm.isIsogenyPair_symm (r ^ c) A E p p' hpair) (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 k π})) gb hgb uA huA
  obtain ⟨hφf, hφ'f, -⟩ := id hpairb
  have hlevb : FakeEllipticCurve.PreservesLevel Eb Ab φ hφf :=
    RQasm.preservesLevel_of_isPullbackVia (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 k π})) E A Eb Ab gb hgb uA huA_sq.w
      (fun t' P => huA_lev' t' P) p' hp' hlev φ hφuA hφf

  have hle : Ideal.span {algebraMap 𝒪 k π} ≤ (pIdeal r k).comap (RingHom.id k) := by
    rw [hπ0, Ideal.span_singleton_eq_bot.mpr rfl]
    exact bot_le
  have hκ1 : (Ideal.quotientMap (pIdeal r k) (RingHom.id k) hle).comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 k π})) = Ideal.Quotient.mk (pIdeal r k) := by
    rw [Ideal.quotientMap_comp_mk, RingHom.comp_id]
  have hκ2 : (Ideal.quotientMap (pIdeal r k) (RingHom.id k) hle).comp (FakeEllipticCurve.Rigidification.residueLeg π ψ) =
      (residueMap ((ψ : Onr →ₐ[𝒪] k) : Onr →+* k)).comp κ := by
    apply Ideal.Quotient.ringHom_ext
    rw [RingHom.comp_assoc, RingHom.comp_assoc, hκ]
    show (Ideal.quotientMap (pIdeal r k) (RingHom.id k) hle).comp
        ((FakeEllipticCurve.Rigidification.residueLeg π ψ).comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 Onr π}))) =
      (residueMap ((ψ : Onr →ₐ[𝒪] k) : Onr →+* k)).comp (Ideal.Quotient.mk (pIdeal r Onr))
    rw [show (FakeEllipticCurve.Rigidification.residueLeg π ψ).comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 Onr π})) =
        ((Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 k π}))).comp ((ψ : Onr →ₐ[𝒪] k) : Onr →+* k) from Ideal.quotientMap_comp_mk _,
      ← RingHom.comp_assoc, hκ1]
    exact (Ideal.quotientMap_comp_mk _).symm

  have c_β₀ : ∀ i, MvPowerSeries.constantCoeff (β₀ i) = 0 := hβ₀.1.constantCoeff
  have hF0 : (fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (k ⧸ pIdeal r k)) ^ (r ^ 0)) = Series.id (k ⧸ pIdeal r k) := by
    funext i
    rw [pow_zero, pow_one]
    rfl
  have hρ' : (Series.map (Ideal.quotientMap (pIdeal r k) (RingHom.id k) hle) (γp.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 k π})))).comp
        ((β₀.map (residueMap ((ψ : Onr →ₐ[𝒪] k) : Onr →+* k))).comp
          (fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (k ⧸ pIdeal r k)) ^ (r ^ 0))) =
      (t.Xbar.act ((r : Zp2 r) ^ e)).comp t.ρ := by
    rw [hF0, Series.comp_id, Series.map_map, hκ1]
    exact hγρ
  have c_ρ : ∀ i, MvPowerSeries.constantCoeff (t.ρ i) = 0 := ht.constantCoeff_ρ
  have c_act : ∀ (m : ℕ) i, MvPowerSeries.constantCoeff (t.Xbar.act ((r : Zp2 r) ^ m) i) = 0 :=
    fun m => (t.Xbar.isLawHom_act _).1

  refine ⟨⟨E, ⟨Eb, gb, hgb, Ab, uA ≫ gA₀, hAbA₀, c, φ, φ', hφf, hpairb, hlevb⟩⟩,
    t.X, θE,
    ⟨t.X, t.n + e, (Series.map (Ideal.quotientMap (pIdeal r k) (RingHom.id k) hle) (γp.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 k π})))).comp
        ((β₀.map (residueMap ((ψ : Onr →ₐ[𝒪] k) : Onr →+* k))).comp
          (fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (k ⧸ pIdeal r k)) ^ (r ^ 0)))⟩,
    hXE, rfl, ?_, ?_, ?_⟩
  ·
    refine ⟨Ideal.quotientMap (pIdeal r k) (RingHom.id k) hle, γp.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 k π})), hκ1, hκ2, ?_, rfl⟩
    intro B'' _ _ _ _ h1 h2 J m hJ s hs PA hPAf hPAA
    have hsnil : ∀ i, IsNilpotent (s i) := fun i => ⟨m + 1, by
      have := Ideal.pow_mem_pow (hs i) (m + 1)
      rw [hJ] at this
      exact (Submodule.mem_bot _).mp this⟩
    have h3 : algebraMap (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'' = (algebraMap k B'').comp ψb := by
      rw [h2, hleg, ← RingHom.comp_assoc, ← h1]
    have hθ := hθA B'' h3 s hsnil
    obtain ⟨hAsq, -⟩ := hA
    have hPAuA : PA ≫ uA = (θA B'' s).1 := by
      apply hAsq.hom_ext
      · rw [Category.assoc, hθ]
        exact hPAA
      · rw [Category.assoc, huA_sq.w, ← Category.assoc, hPAf, (θA B'' s).2, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← h1]
    show PA ≫ φ' ≫ gb = (θE B'' (fun i => MvFormalGroup.nilEval m ((γp.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 k π}))) i) s)).1
    rw [hφ'gb, ← Category.assoc, hPAuA, hγp_germ B'' J m hJ s hs]
    congr 2
    funext i
    exact (RQasm.nilEval_map_of_algebraMap_eq (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 k π})) h1 m (γp i) s).symm
  ·
    refine ⟨ht.1, ht.2.1, ?_⟩
    show FormalODModule.IsIsogenyOfHeight (Φ.map (residueMap ((ψ : Onr →ₐ[𝒪] k) : Onr →+* k))) t.Xbar
      ((Series.map (Ideal.quotientMap (pIdeal r k) (RingHom.id k) hle) (γp.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 k π})))).comp
        ((β₀.map (residueMap ((ψ : Onr →ₐ[𝒪] k) : Onr →+* k))).comp
          (fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (k ⧸ pIdeal r k)) ^ (r ^ 0)))) (4 * (t.n + e))
    rw [hρ']
    exact RQasm.isIsogenyOfHeight_act_pow_comp _ _ t.ρ t.n e (RQasm.hasHeight_map _ t.X 4 ht.2.1) ht.2.2
  ·
    refine ⟨Series.id k, Series.id k, 0, FormalODModule.IsODHom.id _, FormalODModule.IsODHom.id _,
      Series.comp_id _, Series.comp_id _, ?_⟩
    show (t.Xbar.act ((r : Zp2 r) ^ (0 + t.n))).comp (((Series.id k).map (Ideal.Quotient.mk (pIdeal r k))).comp
        ((Series.map (Ideal.quotientMap (pIdeal r k) (RingHom.id k) hle) (γp.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 k π})))).comp
          ((β₀.map (residueMap ((ψ : Onr →ₐ[𝒪] k) : Onr →+* k))).comp
            (fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (k ⧸ pIdeal r k)) ^ (r ^ 0))))) =
      (t.Xbar.act ((r : Zp2 r) ^ (0 + (t.n + e)))).comp t.ρ
    rw [hρ', Series.map_id, Series.id_comp _ (Series.constantCoeff_comp (c_act e) c_ρ),
      ← Series.comp_assoc _ _ _ (c_act e) c_ρ, ← FormalODModule.act_pow_add, zero_add, zero_add]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_rigidifiedCurve_isRigTransport_zero_isIsomorphic_of_quotient_of_isFormalModuleVia
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_rigidifiedCurve_isRigTransport_zero_isIsomorphic_of_quotient_of_isFormalModuleVia (solution)
