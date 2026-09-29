-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_isActBy_scalar_zpow_rigidifiedToG_frobTwist_neg_one_of_comp_verschiebung
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/550ff87b-49df-58c3-a8ba-6b65b78e6d03

import Mathlib.AlgebraicGeometry.Limits
import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_isRigTransport_succ_of_isRigTransport_frobTwist_neg_one
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_parity_mod_two_eq_of_isRigTransport_of_isAdmissible
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_isTranslate_one_of_isRigTransport_add_two
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isPullbackVia_rebase_of_isPullbackVia
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsTranslate_map_ringHom_of_constantCoeff_eq_zero
import Theorems.Thm_CerednikDrinfeld_FormalODModule_hasKernelOfDegree_id
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsTranslate_refl_id
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_parity_eq_and_n_eq_and_eta_eq_of_isRigTransport_of_isRigTransport
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_cover_connected_isPullbackVia_isFormalModuleVia
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullback_levelIff
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsAdmissible_map_ringHom
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_le_one_rigidifiedToG_leg_eq_frobTwist_neg_of_forall_isIdempotentElem
import Theorems.Thm_CerednikDrinfeld_FormalOmega_eq_of_frobTwist_eq_frobTwist_of_isNilpotent_of_nontrivial
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isActBy_scalar_zpow_rigidifiedToG_frobTwist_neg_one_of_comp_verschiebung
p2m_attr_erase "instance" "MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup instTopologicallyFGOfFiniteType AlgebraicGeometry.SquareZero.isLocalRing' AlgebraicGeometry.SquareZero.isLocalRing AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited"
p2m_attr_erase "simp" "MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe"
p2m_attr_erase "simp" "AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.TangentPoints.map_coe AlgebraicGeometry.SquareZero.basePoint_toBase_assoc AlgebraicGeometry.SquareZero.basePoint_toBase AlgebraicGeometry.SquareZero.basePoint_specMap AlgebraicGeometry.SquareZero.basePointOver_coe AlgebraicGeometry.SquareZero.specMap_toBase_assoc AlgebraicGeometry.SquareZero.specMapOver_coe AlgebraicGeometry.RelPicard.TrivialModDeformations.map_coe AlgebraicGeometry.SquareZero.specMap_toBase AlgebraicGeometry.SquareZero.basePoint_specMap_assoc AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.FormalOmega CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

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
    (M : ModuliPackage.{0, 0} r Onr) (hM : M.IsZariskiSheaf)
    (η : ∀ (B : Type) [CommRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B)),
      Rigidified r Φ B → M.obj B ψ hB)
    (hη : (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B))
          (t t' : Rigidified r Φ B), t.IsAdmissible ι ψ → t'.IsAdmissible ι ψ →
          (η B ψ hB t = η B ψ hB t' ↔ t.IsIsomorphic t')) ∧
      (∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] (ψ : Onr →+* B) (ψ' : Onr →+* B')
          (hB : IsNilpotent (r : B)) (hB' : IsNilpotent (r : B')) (f : B →+* B')
          (hf : f.comp ψ = ψ') (t : Rigidified r Φ B), t.IsAdmissible ι ψ →
          η B' ψ' hB' (t.map f) = M.map hB hB' f hf (η B ψ hB t)) ∧
      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B)) (m : M.obj B ψ hB),
          ∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
            ∀ (i : Fin n) (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra B L] [IsLocalization.Away (f i) L]
              (hL : IsNilpotent (r : L)),
              ∃ t : Rigidified r Φ L, t.IsAdmissible ι ((algebraMap B L).comp ψ) ∧
                η L ((algebraMap B L).comp ψ) hL t =
                  M.map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl m))
    (E₀ : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) K₀)
    (hE₀ : Function.Injective E₀ ∧
      ∃ m : ℕ,
        (∀ A : Matrix (Fin 2) (Fin 2) 𝒪, ∃ e, E₀ e = (r : K₀) ^ m • A.map (algebraMap 𝒪 K₀)) ∧
        (∀ e, ∃ A : Matrix (Fin 2) (Fin 2) 𝒪, (r : K₀) ^ m • E₀ e = A.map (algebraMap 𝒪 K₀)))

    (κ : (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) →+* (Onr ⧸ pIdeal r Onr))
    (hκ : κ.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 Onr π})) = Ideal.Quotient.mk (pIdeal r Onr))
    (n₀ : ℕ) (β₀ : Series (Onr ⧸ pIdeal r Onr)) (hβ₀ : FormalODModule.IsIsogenyOfHeight Φ (X₀.map κ) β₀ (4 * n₀))

    (Ξ : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B),
        IsNilpotent (algebraMap 𝒪 B π) → FakeEllipticCurve.RigidifiedCurve r π A₀ B ψ → ModuliPackage.GPoint 𝒪 M B)

    (hΞleg :
      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hconn : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1)
          (x : FakeEllipticCurve.RigidifiedCurve r π A₀ B ψ), ∃ k : ℤ, (Ξ B ψ hB x).ψ = frobTwist Onr Fr k ψ))

    (hΞnat :
      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [IsNoetherianRing B'] [Algebra 𝒪 B']
          (φ : B →ₐ[𝒪] B') (ψ : Onr →ₐ[𝒪] B) (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
          (x : FakeEllipticCurve.RigidifiedCurve r π A₀ B ψ) (x' : FakeEllipticCurve.RigidifiedCurve r π A₀ B' (φ.comp ψ))
          (g : x'.1.A ⟶ x.1.A) (hg : FakeEllipticCurve.IsPullbackVia (φ : B →+* B') x.1 x'.1 g),
          FakeEllipticCurve.Rigidification.IsPullbackVia φ g hg x.2 x'.2 → Ξ B' (φ.comp ψ) hB' x' = (Ξ B ψ hB x).map φ))

    (hΞiso :
      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (hB : IsNilpotent (algebraMap 𝒪 B π))
          (x x' : FakeEllipticCurve.RigidifiedCurve r π A₀ B ψ) (i : x.1.A ≅ x'.1.A) (hi : i.hom ≫ x'.1.f = x.1.f),
          FakeEllipticCurve.IsoVia x.1 x'.1 i hi →
          (∃ (ib : x.2.Eb.A ⟶ x'.2.Eb.A) (_ : ib ≫ x'.2.gb = x.2.gb ≫ i.hom) (_ : ib ≫ x'.2.Eb.f = x.2.Eb.f)
            (uA : x'.2.Ab.A ⟶ x.2.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) x.2.Ab x'.2.Ab uA) (_ : uA ≫ x.2.gA = x'.2.gA)
            (i₁ j₁ : ℕ),
            ib ≫ x'.2.φ ≫ uA ≫ x.2.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = x.2.φ ≫ x.2.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩) →
            Ξ B ψ hB x = Ξ B ψ hB x'))

    (hΞdef :
      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hconn : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1)
          (hBr : IsNilpotent ((r : ℕ) : B))
          (x : FakeEllipticCurve.RigidifiedCurve r π A₀ B ψ) (X : FormalODModule r B) (θ : RelativeGroupLaw.FormalCoordinates x.1.f 2),
          x.1.IsFormalModuleVia coord X θ →
          ∃ (j : ℕ) (t : Rigidified r Φ B), j ≤ 1 ∧ t.X = X ∧
            FakeEllipticCurve.Rigidification.IsRigTransport θ₀ κ β₀ x.2 θ j t ∧
            t.IsAdmissible ι ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B) ∧
            Ξ B ψ hB x = ⟨frobTwist Onr Fr (-(j : ℤ)) ψ, hBr, η B ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B) hBr t⟩))

    (A₀r : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})) (prA : A₀r.A ⟶ A₀.A)
    (hprA : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π (Fr.symm : Onr →ₐ[𝒪] Onr)) A₀ A₀r prA)
    (F : A₀.A ⟶ A₀r.A) (hF : F ≫ A₀r.f = A₀.f) (V : A₀r.A ⟶ A₀.A) (hV : V ≫ A₀.f = A₀r.f)
    (F_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (P Q : SchemeHomOver t A₀.f),
      mapPt F hF (A₀.L.mul t P Q) = A₀r.L.mul t (mapPt F hF P) (mapPt F hF Q))
    (V_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (P Q : SchemeHomOver t A₀r.f),
      mapPt V hV (A₀r.L.mul t P Q) = A₀.L.mul t (mapPt V hV P) (mapPt V hV Q))
    (F_act : ∀ x : ↥Λ, A₀.act x ≫ F = F ≫ A₀r.act x) (V_act : ∀ x : ↥Λ, A₀r.act x ≫ V = V ≫ A₀.act x)
    (F_lev : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (P : SchemeHomOver t A₀.f),
      FactorsThrough A₀.lev P → FactorsThrough A₀r.lev (mapPt F hF P))
    (V_lev : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (Q : SchemeHomOver t A₀r.f),
      FactorsThrough A₀r.lev Q → FactorsThrough A₀.lev (mapPt V hV Q))
    (V_F : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (P : SchemeHomOver t A₀.f),
      mapPt V hV (mapPt F hF P) = nsmulPt A₀.L t r P)
    (F_V : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (Q : SchemeHomOver t A₀r.f),
      mapPt F hF (mapPt V hV Q) = nsmulPt A₀r.L t r Q)
    (V_frob : ∀ (C : Type) [CommRing C] [CharP C r] (x : Spec (CommRingCat.of C) ⟶ A₀r.A),
      x ≫ V = Spec.map (CommRingCat.ofHom (frobenius C r)) ≫ x ≫ prA)

    (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (hBπ : IsNilpotent (algebraMap 𝒪 B π))
    (hconn : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1)
    (E : FakeEllipticCurve Λ N B) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E)
    (ρp : FakeEllipticCurve.Rigidification r π A₀ (frobTwist Onr Fr (-1) ψ) E)
    (ub : ρ.Eb.A ⟶ ρp.Eb.A) (hub : ub ≫ ρp.gb = ρ.gb) (hub' : ub ≫ ρp.Eb.f = ρ.Eb.f)
    (gA' : ρp.Ab.A ⟶ A₀r.A) (hgA' : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π ψ) A₀r ρp.Ab gA')
    (hgA'' : gA' ≫ prA = ρp.gA)
    (Fb : ρ.Ab.A ⟶ ρp.Ab.A) (hFb : Fb ≫ gA' = ρ.gA ≫ F) (hFb' : Fb ≫ ρp.Ab.f = ρ.Ab.f)
    (Vb : ρp.Ab.A ⟶ ρ.Ab.A) (hVb : Vb ≫ ρ.gA = gA' ≫ V) (hVb' : Vb ≫ ρ.Ab.f = ρp.Ab.f)
    (hd : ρp.d = ρ.d + 1) (hφ : ub ≫ ρp.φ = ρ.φ ≫ Fb) (hφ' : ρp.φ' = Vb ≫ ρ.φ' ≫ ub) :
    ∃ c : ℤ,
      ModuliPackage.G.IsActBy ι Φ η Fr E₀ ((Units.map (algebraMap K₀ (Matrix (Fin 2) (Fin 2) K₀)).toMonoidHom
              (Units.mk0 (r : K₀) (Nat.cast_ne_zero.mpr (Fact.out : r.Prime).ne_zero))) ^ c)
        (Ξ B ψ hBπ ⟨E, ρ⟩) (Ξ B (frobTwist Onr Fr (-1) ψ) hBπ ⟨E, ρp⟩) := by
  have hBr : IsNilpotent ((r : ℕ) : B) := by
    have hmem : ((r : ℕ) : 𝒪) ∈ Ideal.span {π} := hunr ▸ Ideal.subset_span rfl
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hmem
    have : ((r : ℕ) : B) = algebraMap 𝒪 B c * algebraMap 𝒪 B π := by rw [← map_mul, hc, map_natCast]
    rw [this]
    exact Commute.isNilpotent_mul_left (Commute.all _ _) hBπ
  have hone : (((1 : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) : MvFormalGroup.End Φ.F).toPowerSeries) =
      Series.id (Onr ⧸ pIdeal r Onr) := rfl
  rcases subsingleton_or_nontrivial B with hsub | hnt
  ·
    refine ⟨0, 1, 0, 0, ?_, ?_, ?_, 0, Fin.elim0, Subsingleton.elim _ _, fun i => i.elim0⟩
    · simp
    · rw [hone, mul_zero, pow_zero]; exact CerednikDrinfeld.FormalODModule.hasKernelOfDegree_id _
    · exact AlgHom.ext fun _ => Subsingleton.elim _ _
  ·

    have ftw : ∀ (a b : ℤ) {C : Type} [CommRing C] [Algebra 𝒪 C] (χ : Onr →ₐ[𝒪] C),
        frobTwist Onr Fr a (frobTwist Onr Fr b χ) = frobTwist Onr Fr (b + a) χ := by
      intro a b C _ _ χ
      apply AlgHom.ext; intro o
      simp only [frobTwist, AlgHom.comp_apply, zpow_add]
      rfl
    have ftw_comp : ∀ (a : ℤ) {C C' : Type} [CommRing C] [Algebra 𝒪 C] [CommRing C'] [Algebra 𝒪 C'] (g : C →ₐ[𝒪] C') (χ : Onr →ₐ[𝒪] C),
        g.comp (frobTwist Onr Fr a χ) = frobTwist Onr Fr a (g.comp χ) := by
      intro a C C' _ _ _ _ g χ; rfl

    obtain ⟨jg, hjg, hlegx⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.exists_le_one_rigidifiedToG_leg_eq_frobTwist_neg_of_forall_isIdempotentElem
      hrr hrN 𝒪 hdvr π hπ hcomplete hres hunr K₀ Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr hB Λ hΛ hΛℤ coord hcoord A₀ X₀ hX₀ θ₀ hA₀ ι Φ hΦ hΦ4 M hM η hη E₀ hE₀ κ hκ n₀ β₀ hβ₀ Ξ hΞleg hΞnat hΞiso hΞdef B ψ hBπ hconn ⟨E, ρ⟩
    obtain ⟨jg', hjg', hlegx'⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.exists_le_one_rigidifiedToG_leg_eq_frobTwist_neg_of_forall_isIdempotentElem
      hrr hrN 𝒪 hdvr π hπ hcomplete hres hunr K₀ Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr hB Λ hΛ hΛℤ coord hcoord A₀ X₀ hX₀ θ₀ hA₀ ι Φ hΦ hΦ4 M hM η hη E₀ hE₀ κ hκ n₀ β₀ hβ₀ Ξ hΞleg hΞnat hΞiso hΞdef B (frobTwist Onr Fr (-1) ψ) hBπ hconn ⟨E, ρp⟩

    obtain ⟨s, hs, hpieces⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.exists_cover_connected_isPullbackVia_isFormalModuleVia coord hcoord B hBr E

    have piece : ∀ c ∈ s, ¬ IsNilpotent c →
        ∃ (j j' : ℕ) (t t' : Rigidified r Φ (Localization.Away c)),
          j = jg ∧ j' = jg' ∧ j % 2 = (j' + 1) % 2 ∧ 2 * t'.n + j = 2 * t.n + (j' + 1) ∧ t'.X = t.X ∧
          t.IsAdmissible ι ((algebraMap B (Localization.Away c)).comp ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B)) ∧
          t'.IsAdmissible ι ((algebraMap B (Localization.Away c)).comp ((frobTwist Onr Fr (-(j' : ℤ)) (frobTwist Onr Fr (-1) ψ) : Onr →ₐ[𝒪] B) : Onr →+* B)) ∧
          (∀ hL₀ : IsNilpotent ((r : ℕ) : (Localization.Away c)),
            (Ξ B ψ hBπ ⟨E, ρ⟩).map (IsScalarTower.toAlgHom 𝒪 B (Localization.Away c)) =
              ⟨(IsScalarTower.toAlgHom 𝒪 B (Localization.Away c)).comp (frobTwist Onr Fr (-(j : ℤ)) ψ), hL₀,
                η (Localization.Away c) _ hL₀ t⟩ ∧
            (Ξ B (frobTwist Onr Fr (-1) ψ) hBπ ⟨E, ρp⟩).map (IsScalarTower.toAlgHom 𝒪 B (Localization.Away c)) =
              ⟨(IsScalarTower.toAlgHom 𝒪 B (Localization.Away c)).comp (frobTwist Onr Fr (-(j' : ℤ)) (frobTwist Onr Fr (-1) ψ)), hL₀,
                η (Localization.Away c) _ hL₀ t'⟩) ∧
          Rigidified.IsTranslate (Series.id (Onr ⧸ pIdeal r Onr)) (1 - j) 0
              ((algebraMap B (Localization.Away c)).comp ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B)) t t' := by
      intro c hcs hcn
      haveI : Nontrivial (Localization.Away c) := by
        rw [← not_subsingleton_iff_nontrivial, IsLocalization.subsingleton_iff (M := Submonoid.powers c)]
        rintro ⟨n, hn⟩; exact hcn ⟨n, hn⟩
      haveI : IsNoetherianRing (Localization.Away c) := IsLocalization.isNoetherianRing (Submonoid.powers c) _ inferInstance
      obtain ⟨hconnL, hcoordsL⟩ := hpieces c hcs
      have hBL : IsNilpotent (algebraMap 𝒪 (Localization.Away c) π) := by
        rw [IsScalarTower.algebraMap_apply 𝒪 B (Localization.Away c) π]; exact hBπ.map _
      have hLr : IsNilpotent ((r : ℕ) : (Localization.Away c)) := by simpa only [map_natCast] using hBr.map (algebraMap B (Localization.Away c))

      obtain ⟨EL, g₀, hgsq, gmul, gact, glev, -⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_levelIff (algebraMap B (Localization.Away c)) E
      have hg₀ : FakeEllipticCurve.IsPullbackVia (algebraMap B (Localization.Away c)) E EL g₀ := ⟨hgsq, gmul, gact, glev⟩
      obtain ⟨ρL, ρmL, hρL, hρmL, ubL, hubL, hubL', gA'L, hgA'L, hgA''L, FbL, hFbL, hFbL', VbL, hVbL, hVbL', hdL, hφL, hφ'L⟩ :=
        CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_isPullbackVia_rebase_of_isPullbackVia 𝒪 π Onr ((Fr ^ (-1 : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) Λ A₀ A₀r prA F V B ψ E ρ ρp
          ub hub hub' gA' hgA' hgA'' Fb hFb hFb' Vb hVb hVb' hd hφ hφ' (Localization.Away c) (IsScalarTower.toAlgHom 𝒪 B (Localization.Away c)) EL g₀ hg₀
      have n1 := hΞnat B (Localization.Away c) (IsScalarTower.toAlgHom 𝒪 B (Localization.Away c)) ψ hBπ hBL ⟨E, ρ⟩ ⟨EL, ρL⟩ g₀ hg₀ hρL
      have n2 := hΞnat B (Localization.Away c) (IsScalarTower.toAlgHom 𝒪 B (Localization.Away c)) (frobTwist Onr Fr (-1) ψ) hBπ hBL ⟨E, ρp⟩ ⟨EL, ρmL⟩ g₀ hg₀ hρmL

      obtain ⟨XL, θL, hXL⟩ := hcoordsL EL g₀ hg₀
      obtain ⟨j, t, hj, htX, htr, hadm, hΞ1⟩ := hΞdef (Localization.Away c) ((IsScalarTower.toAlgHom 𝒪 B (Localization.Away c)).comp ψ) hBL hconnL hLr ⟨EL, ρL⟩ XL θL hXL
      obtain ⟨j', t', hj', ht'X, htr', hadm', hΞ2⟩ :=
        hΞdef (Localization.Away c) ((IsScalarTower.toAlgHom 𝒪 B (Localization.Away c)).comp (frobTwist Onr Fr (-1) ψ)) hBL hconnL hLr ⟨EL, ρmL⟩ XL θL hXL

      have hjj : j = jg := by
        have e := congrArg ModuliPackage.GPoint.ψ (n1.symm.trans hΞ1)
        rw [ModuliPackage.GPoint.map_ψ, hlegx, ftw_comp] at e
        have := CerednikDrinfeld.FormalOmega.eq_of_frobTwist_eq_frobTwist_of_isNilpotent_of_nontrivial π Onr Fr hOnr_closed hFr (Localization.Away c) hBL ((IsScalarTower.toAlgHom 𝒪 B (Localization.Away c)).comp ψ) _ _ e
        omega
      have hjj' : j' = jg' := by
        have e := congrArg ModuliPackage.GPoint.ψ (n2.symm.trans hΞ2)
        rw [ModuliPackage.GPoint.map_ψ, hlegx', ftw_comp] at e
        have := CerednikDrinfeld.FormalOmega.eq_of_frobTwist_eq_frobTwist_of_isNilpotent_of_nontrivial π Onr Fr hOnr_closed hFr (Localization.Away c) hBL ((IsScalarTower.toAlgHom 𝒪 B (Localization.Away c)).comp (frobTwist Onr Fr (-1) ψ)) _ _ e
        omega
      subst hjj hjj'

      have ht0 : ∀ i, MvPowerSeries.constantCoeff (t.ρ i) = 0 := hadm.2.2.1.1.1
      have ht'0 : ∀ i, MvPowerSeries.constantCoeff (t'.ρ i) = 0 := hadm'.2.2.1.1.1
      have htr'' := CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.isRigTransport_succ_of_isRigTransport_frobTwist_neg_one
        hrr hrN 𝒪 hdvr π hπ hcomplete hres hunr K₀ Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr hB Λ hΛ hΛℤ coord hcoord A₀ X₀ hX₀ θ₀ hA₀ ι Φ hΦ hΦ4 M hM η hη E₀ hE₀ κ hκ n₀ β₀ hβ₀ Ξ hΞleg hΞnat hΞiso hΞdef
        A₀r prA hprA F hF V hV F_hom V_hom F_act V_act F_lev V_lev V_F F_V V_frob
        (Localization.Away c) ((IsScalarTower.toAlgHom 𝒪 B (Localization.Away c)).comp ψ) hBL hconnL EL ρL ρmL ubL hubL hubL' gA'L hgA'L hgA''L FbL hFbL hFbL' VbL hVbL hVbL' hdL hφL hφ'L
        XL θL hXL j' t' ht'0 htr'
      have eqleg : frobTwist Onr Fr (-(j' : ℤ)) ((IsScalarTower.toAlgHom 𝒪 B (Localization.Away c)).comp (frobTwist Onr Fr (-1) ψ)) =
          frobTwist Onr Fr (-((j' + 1 : ℕ) : ℤ)) ((IsScalarTower.toAlgHom 𝒪 B (Localization.Away c)).comp ψ) := by
        rw [ftw_comp, ftw]; congr 1; push_cast; ring
      have hadm₂ : t'.IsAdmissible ι ((frobTwist Onr Fr (-((j' + 1 : ℕ) : ℤ)) ((IsScalarTower.toAlgHom 𝒪 B (Localization.Away c)).comp ψ) : Onr →ₐ[𝒪] (Localization.Away c)) : Onr →+* (Localization.Away c)) := by
        rw [← eqleg]; exact hadm'
      obtain ⟨hpar, hn2⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.parity_mod_two_eq_of_isRigTransport_of_isAdmissible
        hrr hrN 𝒪 hdvr π hπ hcomplete hres hunr K₀ Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr hB Λ hΛ hΛℤ coord hcoord A₀ X₀ hX₀ θ₀ hA₀ ι Φ hΦ hΦ4 M hM η hη E₀ hE₀ κ hκ n₀ β₀ hβ₀
        (Localization.Away c) ((IsScalarTower.toAlgHom 𝒪 B (Localization.Away c)).comp ψ) hBL hconnL hLr ⟨EL, ρL⟩ XL θL hXL j t htX htr hadm (j' + 1) t' ht'X htr'' hadm₂
      interval_cases j <;> interval_cases j'
      · omega
      ·
        refine ⟨0, 1, t, t', rfl, rfl, hpar, hn2, by rw [ht'X, htX], hadm, hadm', fun hL₀ => ⟨n1.symm.trans hΞ1, n2.symm.trans hΞ2⟩, ?_⟩
        exact CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.isTranslate_one_of_isRigTransport_add_two
          hrr hrN 𝒪 hdvr π hπ hcomplete hres hunr K₀ Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr hB Λ hΛ hΛℤ coord hcoord A₀ X₀ hX₀ θ₀ hA₀ ι Φ hΦ hΦ4 M hM η hη E₀ hE₀ κ hκ n₀ β₀ hβ₀
          (Localization.Away c) ((IsScalarTower.toAlgHom 𝒪 B (Localization.Away c)).comp ψ) hBL ⟨EL, ρL⟩ XL θL hXL 0 t htX ht0 htr t' ht'X ht'0 htr'' (by omega)
      ·
        have hadm₃ : t'.IsAdmissible ι ((frobTwist Onr Fr (-((1 : ℕ) : ℤ)) ((IsScalarTower.toAlgHom 𝒪 B (Localization.Away c)).comp ψ) : Onr →ₐ[𝒪] (Localization.Away c)) : Onr →+* (Localization.Away c)) := hadm₂
        obtain ⟨-, -, hηeq⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.parity_eq_and_n_eq_and_eta_eq_of_isRigTransport_of_isRigTransport
          hrr hrN 𝒪 hdvr π hπ hcomplete hres hunr K₀ Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr hB Λ hΛ hΛℤ coord hcoord A₀ X₀ hX₀ θ₀ hA₀ ι Φ hΦ hΦ4 M hM η hη E₀ hE₀ κ hκ n₀ β₀ hβ₀
          (Localization.Away c) ((IsScalarTower.toAlgHom 𝒪 B (Localization.Away c)).comp ψ) hBL hconnL hLr ⟨EL, ρL⟩ XL θL hXL XL θL hXL 1 t le_rfl htX htr hadm 1 t' le_rfl ht'X htr'' hadm₃
        refine ⟨1, 0, t, t, rfl, rfl, hpar, by omega, rfl, hadm, ?_, fun hL₀ => ⟨n1.symm.trans hΞ1, ?_⟩, ?_⟩
        · have e01 : frobTwist Onr Fr (-((0 : ℕ) : ℤ)) (frobTwist Onr Fr (-1) ψ) = frobTwist Onr Fr (-((1 : ℕ) : ℤ)) ψ := by
            rw [ftw]; norm_num
          rw [e01]; exact hadm
        · rw [n2.symm.trans hΞ2]
          refine ModuliPackage.GPoint.ext' ?_ ?_
          · exact eqleg.trans rfl
          · have hc2 : ∀ (a b : Onr →+* (Localization.Away c)) (hab : a = b) (ha : IsNilpotent ((r : ℕ) : (Localization.Away c))) (hb : IsNilpotent ((r : ℕ) : (Localization.Away c)))
                (u : Rigidified r Φ (Localization.Away c)), HEq (η (Localization.Away c) a ha u) (η (Localization.Away c) b hb u) := by
              intro a b hab ha hb u; subst hab; rfl
            have eAC : ((frobTwist Onr Fr (-((0 : ℕ) : ℤ)) ((IsScalarTower.toAlgHom 𝒪 B (Localization.Away c)).comp (frobTwist Onr Fr (-1) ψ)) : Onr →ₐ[𝒪] (Localization.Away c)) : Onr →+* (Localization.Away c)) =
                ((frobTwist Onr Fr (-((0 + 1 : ℕ) : ℤ)) ((IsScalarTower.toAlgHom 𝒪 B (Localization.Away c)).comp ψ) : Onr →ₐ[𝒪] (Localization.Away c)) : Onr →+* (Localization.Away c)) :=
              congrArg (fun φ : Onr →ₐ[𝒪] (Localization.Away c) => (φ : Onr →+* (Localization.Away c))) eqleg
            exact (hc2 _ _ eAC hLr hLr t').trans ((heq_of_eq hηeq.symm).trans (hc2 _ _ eAC.symm hLr hL₀ t))
        · exact CerednikDrinfeld.SpecialFormal.Rigidified.IsTranslate.refl_id _ t
      · omega

    have hex : ∃ c ∈ s, ¬ IsNilpotent c := by
      by_contra hall
      push_neg at hall
      have hle : (⊤ : Ideal B) ≤ nilradical B := by
        rw [← hs]; exact Ideal.span_le.2 (fun c hc => mem_nilradical.2 (hall c hc))
      obtain ⟨n, hn⟩ := mem_nilradical.1 (hle Submodule.mem_top : (1 : B) ∈ nilradical B)
      exact one_ne_zero (by rwa [one_pow] at hn)
    obtain ⟨c₀, hc₀s, hc₀⟩ := hex
    obtain ⟨j₀, j₀', t₀, t₀', hj₀, hj₀', hpar₀, -⟩ := piece c₀ hc₀s hc₀
    have hrel : jg' + jg = 1 := by omega

    classical
    have hs' : Ideal.span ((s.filter fun c => ¬ IsNilpotent c : Finset B) : Set B) = ⊤ := by
      by_contra hne
      obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
      have hnil : nilradical B ≤ m := nilradical_le_prime m
      have hsm : Ideal.span (s : Set B) ≤ m := Ideal.span_le.2 fun c hc => by
        by_cases hcn : IsNilpotent c
        · exact hnil (mem_nilradical.2 hcn)
        · exact hle (Ideal.subset_span (by simpa [Finset.mem_filter] using And.intro hc hcn))
      rw [hs] at hsm
      exact hm.ne_top (top_le_iff.1 hsm)
    let f : Fin (s.filter fun c => ¬ IsNilpotent c).card → B := fun k => (((s.filter fun c => ¬ IsNilpotent c).equivFin.symm k : ↥(s.filter fun c => ¬ IsNilpotent c)) : B)
    have hrange : Set.range f = ((s.filter fun c => ¬ IsNilpotent c : Finset B) : Set B) := by
      ext y
      constructor
      · rintro ⟨k, rfl⟩; exact ((s.filter fun c => ¬ IsNilpotent c).equivFin.symm k).2
      · intro hy; exact ⟨(s.filter fun c => ¬ IsNilpotent c).equivFin ⟨y, hy⟩, by simp [f]⟩
    have hf_mem : ∀ k, f k ∈ s ∧ ¬ IsNilpotent (f k) := fun k =>
      Finset.mem_filter.1 ((s.filter fun c => ¬ IsNilpotent c).equivFin.symm k).2
    interval_cases jg
    ·
      have hjg'1 : jg' = 1 := by omega
      subst hjg'1
      refine ⟨1, 1, 1, 0, ?_, ?_, ?_, _, f, (by rw [hrange]; exact hs'), ?_⟩
      ·
        have hr0 : (r : K₀) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : r.Prime).ne_zero
        simp [Units.smul_def, Algebra.algebraMap_eq_smul_one, smul_smul, hr0]

      ·
        rw [hone, mul_zero, pow_zero]; exact CerednikDrinfeld.FormalODModule.hasKernelOfDegree_id _
      ·
        rw [hlegx', hlegx, ftw, ftw]
        congr 1
      ·
        intro i L _ _ _ hL
        letI : Algebra 𝒪 L := ((algebraMap B L).comp (algebraMap 𝒪 B)).toAlgebra
        haveI : IsScalarTower 𝒪 B L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
        obtain ⟨hcs, hcn⟩ := hf_mem i
        obtain ⟨j, j', t, t', hj, hj', hpar, hn2, htX, hadm, hadm', hmaps, htr0⟩ := piece (f i) hcs hcn
        subst hj hj'
        haveI : Nontrivial (Localization.Away (f i)) := by
          rw [← not_subsingleton_iff_nontrivial, IsLocalization.subsingleton_iff (M := Submonoid.powers (f i))]
          rintro ⟨n, hn⟩; exact hcn ⟨n, hn⟩
        haveI : IsNoetherianRing (Localization.Away (f i)) := IsLocalization.isNoetherianRing (Submonoid.powers (f i)) _ inferInstance
        haveI : IsNoetherianRing L := IsLocalization.isNoetherianRing (Submonoid.powers (f i)) _ inferInstance
        have hL₀ : IsNilpotent ((r : ℕ) : Localization.Away (f i)) := by simpa only [map_natCast] using hBr.map (algebraMap B _)
        obtain ⟨hmx, hmx'⟩ := hmaps hL₀

        let h : Localization.Away (f i) ≃ₐ[B] L := IsLocalization.algEquiv (Submonoid.powers (f i)) _ _
        let g : Localization.Away (f i) →+* L := h.toAlgHom.toRingHom
        have hg : g.comp (algebraMap B (Localization.Away (f i))) = algebraMap B L := h.toAlgHom.comp_algebraMap
        let gO : Localization.Away (f i) →ₐ[𝒪] L := h.toAlgHom.restrictScalars 𝒪
        have hgO : (IsScalarTower.toAlgHom 𝒪 B L) = gO.comp (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))) := by
          apply AlgHom.ext; intro y
          show algebraMap B L y = h (algebraMap B _ y)
          exact (h.toAlgHom.commutes y).symm

        have hηg : ∀ (χ : Onr →+* Localization.Away (f i)) (u : Rigidified r Φ (Localization.Away (f i))),
            u.IsAdmissible ι χ → η L (g.comp χ) hL (u.map g) = M.map hL₀ hL g rfl (η _ χ hL₀ u) :=
          fun χ u hu => hη.2.1 _ L χ (g.comp χ) hL₀ hL g rfl u hu

        have hηc : ∀ (a b : Onr →+* L) (hab : a = b) (ha : IsNilpotent ((r : ℕ) : L)) (hb : IsNilpotent ((r : ℕ) : L)) (u : Rigidified r Φ L),
            HEq (η L a ha u) (η L b hb u) := by
          intro a b hab ha hb u; subst hab; rfl

        refine ⟨t.map g, t'.map g, ?_, ?_, ?_, ?_, ?_⟩
        · have ha := CerednikDrinfeld.SpecialFormal.Rigidified.IsAdmissible.map_ringHom ι _ g t hadm
          rw [← RingHom.comp_assoc, hg] at ha
          rw [hlegx]
          exact ha
        · have ha := CerednikDrinfeld.SpecialFormal.Rigidified.IsAdmissible.map_ringHom ι _ g t' hadm'
          rw [← RingHom.comp_assoc, hg] at ha
          rw [hlegx']
          exact ha
        ·
          have e1 : (Ξ B ψ hBπ ⟨E, ρ⟩).map (IsScalarTower.toAlgHom 𝒪 B L) = ((Ξ B ψ hBπ ⟨E, ρ⟩).map (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i)))).map gO := by
            rw [hgO, ModuliPackage.GPoint.map_comp]
          rw [hmx] at e1
          have e2 : ((⟨((IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))).comp (frobTwist Onr Fr (-((0 : ℕ) : ℤ)) ψ)), hL₀, η (Localization.Away (f i)) _ hL₀ t⟩ : ModuliPackage.GPoint 𝒪 M (Localization.Away (f i))).map gO) =
              ⟨gO.comp ((IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))).comp (frobTwist Onr Fr (-((0 : ℕ) : ℤ)) ψ)), by simpa only [map_natCast] using hBr.map (algebraMap B L),
                η L (g.comp (((IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))).comp (frobTwist Onr Fr (-((0 : ℕ) : ℤ)) ψ)) : Onr →+* (Localization.Away (f i)))) hL (t.map g)⟩ := by
            refine ModuliPackage.GPoint.ext' ?_ ?_
            · rfl
            simp only [ModuliPackage.GPoint.map_pt]
            exact heq_of_eq (hηg _ t hadm).symm
          rw [e2] at e1
          simp only [ModuliPackage.GPoint.map] at e1
          injection e1 with el ep
          have hab : g.comp (((IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))).comp (frobTwist Onr Fr (-((0 : ℕ) : ℤ)) ψ)) : Onr →+* (Localization.Away (f i))) = (algebraMap B L).comp ((Ξ B ψ hBπ ⟨E, ρ⟩).ψ : Onr →+* B) := by
            have := congrArg (fun (φ : Onr →ₐ[𝒪] L) => (φ : Onr →+* L)) el
            exact this.symm
          exact eq_of_heq ((hηc _ _ hab hL _ (t.map g)).symm.trans ep.symm)
        ·
          have e1 : (Ξ B (frobTwist Onr Fr (-1) ψ) hBπ ⟨E, ρp⟩).map (IsScalarTower.toAlgHom 𝒪 B L) = ((Ξ B (frobTwist Onr Fr (-1) ψ) hBπ ⟨E, ρp⟩).map (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i)))).map gO := by
            rw [hgO, ModuliPackage.GPoint.map_comp]
          rw [hmx'] at e1
          have e2 : ((⟨((IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))).comp (frobTwist Onr Fr (-((1 : ℕ) : ℤ)) (frobTwist Onr Fr (-1) ψ))), hL₀, η (Localization.Away (f i)) _ hL₀ t'⟩ : ModuliPackage.GPoint 𝒪 M (Localization.Away (f i))).map gO) =
              ⟨gO.comp ((IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))).comp (frobTwist Onr Fr (-((1 : ℕ) : ℤ)) (frobTwist Onr Fr (-1) ψ))), by simpa only [map_natCast] using hBr.map (algebraMap B L),
                η L (g.comp (((IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))).comp (frobTwist Onr Fr (-((1 : ℕ) : ℤ)) (frobTwist Onr Fr (-1) ψ))) : Onr →+* (Localization.Away (f i)))) hL (t'.map g)⟩ := by
            refine ModuliPackage.GPoint.ext' ?_ ?_
            · rfl
            simp only [ModuliPackage.GPoint.map_pt]
            exact heq_of_eq (hηg _ t' hadm').symm
          rw [e2] at e1
          simp only [ModuliPackage.GPoint.map] at e1
          injection e1 with el ep
          have hab : g.comp (((IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))).comp (frobTwist Onr Fr (-((1 : ℕ) : ℤ)) (frobTwist Onr Fr (-1) ψ))) : Onr →+* (Localization.Away (f i))) = (algebraMap B L).comp ((Ξ B (frobTwist Onr Fr (-1) ψ) hBπ ⟨E, ρp⟩).ψ : Onr →+* B) := by
            have := congrArg (fun (φ : Onr →ₐ[𝒪] L) => (φ : Onr →+* L)) el
            exact this.symm
          exact eq_of_heq ((hηc _ _ hab hL _ (t'.map g)).symm.trans ep.symm)
        · have hT := CerednikDrinfeld.SpecialFormal.Rigidified.IsTranslate.map_ringHom_of_constantCoeff_eq_zero (Series.id _) (1 - 0) 0 _ g t t' hadm.2.2.1.1.1 hadm'.2.2.1.1.1 (fun i => MvPowerSeries.constantCoeff_X i) htr0
          rw [← RingHom.comp_assoc, hg] at hT
          rw [hone, hlegx]
          exact hT

    ·
      have hjg'0 : jg' = 0 := by omega
      subst hjg'0
      refine ⟨0, 1, 0, 0, ?_, ?_, ?_, _, f, (by rw [hrange]; exact hs'), ?_⟩
      ·
        simp

      ·
        rw [hone, mul_zero, pow_zero]; exact CerednikDrinfeld.FormalODModule.hasKernelOfDegree_id _
      ·
        rw [hlegx', hlegx, ftw, ftw]
        congr 1
      ·
        intro i L _ _ _ hL
        letI : Algebra 𝒪 L := ((algebraMap B L).comp (algebraMap 𝒪 B)).toAlgebra
        haveI : IsScalarTower 𝒪 B L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
        obtain ⟨hcs, hcn⟩ := hf_mem i
        obtain ⟨j, j', t, t', hj, hj', hpar, hn2, htX, hadm, hadm', hmaps, htr0⟩ := piece (f i) hcs hcn
        subst hj hj'
        haveI : Nontrivial (Localization.Away (f i)) := by
          rw [← not_subsingleton_iff_nontrivial, IsLocalization.subsingleton_iff (M := Submonoid.powers (f i))]
          rintro ⟨n, hn⟩; exact hcn ⟨n, hn⟩
        haveI : IsNoetherianRing (Localization.Away (f i)) := IsLocalization.isNoetherianRing (Submonoid.powers (f i)) _ inferInstance
        haveI : IsNoetherianRing L := IsLocalization.isNoetherianRing (Submonoid.powers (f i)) _ inferInstance
        have hL₀ : IsNilpotent ((r : ℕ) : Localization.Away (f i)) := by simpa only [map_natCast] using hBr.map (algebraMap B _)
        obtain ⟨hmx, hmx'⟩ := hmaps hL₀

        let h : Localization.Away (f i) ≃ₐ[B] L := IsLocalization.algEquiv (Submonoid.powers (f i)) _ _
        let g : Localization.Away (f i) →+* L := h.toAlgHom.toRingHom
        have hg : g.comp (algebraMap B (Localization.Away (f i))) = algebraMap B L := h.toAlgHom.comp_algebraMap
        let gO : Localization.Away (f i) →ₐ[𝒪] L := h.toAlgHom.restrictScalars 𝒪
        have hgO : (IsScalarTower.toAlgHom 𝒪 B L) = gO.comp (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))) := by
          apply AlgHom.ext; intro y
          show algebraMap B L y = h (algebraMap B _ y)
          exact (h.toAlgHom.commutes y).symm

        have hηg : ∀ (χ : Onr →+* Localization.Away (f i)) (u : Rigidified r Φ (Localization.Away (f i))),
            u.IsAdmissible ι χ → η L (g.comp χ) hL (u.map g) = M.map hL₀ hL g rfl (η _ χ hL₀ u) :=
          fun χ u hu => hη.2.1 _ L χ (g.comp χ) hL₀ hL g rfl u hu

        have hηc : ∀ (a b : Onr →+* L) (hab : a = b) (ha : IsNilpotent ((r : ℕ) : L)) (hb : IsNilpotent ((r : ℕ) : L)) (u : Rigidified r Φ L),
            HEq (η L a ha u) (η L b hb u) := by
          intro a b hab ha hb u; subst hab; rfl

        refine ⟨t.map g, t'.map g, ?_, ?_, ?_, ?_, ?_⟩
        · have ha := CerednikDrinfeld.SpecialFormal.Rigidified.IsAdmissible.map_ringHom ι _ g t hadm
          rw [← RingHom.comp_assoc, hg] at ha
          rw [hlegx]
          exact ha
        · have ha := CerednikDrinfeld.SpecialFormal.Rigidified.IsAdmissible.map_ringHom ι _ g t' hadm'
          rw [← RingHom.comp_assoc, hg] at ha
          rw [hlegx']
          exact ha
        ·
          have e1 : (Ξ B ψ hBπ ⟨E, ρ⟩).map (IsScalarTower.toAlgHom 𝒪 B L) = ((Ξ B ψ hBπ ⟨E, ρ⟩).map (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i)))).map gO := by
            rw [hgO, ModuliPackage.GPoint.map_comp]
          rw [hmx] at e1
          have e2 : ((⟨((IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))).comp (frobTwist Onr Fr (-((1 : ℕ) : ℤ)) ψ)), hL₀, η (Localization.Away (f i)) _ hL₀ t⟩ : ModuliPackage.GPoint 𝒪 M (Localization.Away (f i))).map gO) =
              ⟨gO.comp ((IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))).comp (frobTwist Onr Fr (-((1 : ℕ) : ℤ)) ψ)), by simpa only [map_natCast] using hBr.map (algebraMap B L),
                η L (g.comp (((IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))).comp (frobTwist Onr Fr (-((1 : ℕ) : ℤ)) ψ)) : Onr →+* (Localization.Away (f i)))) hL (t.map g)⟩ := by
            refine ModuliPackage.GPoint.ext' ?_ ?_
            · rfl
            simp only [ModuliPackage.GPoint.map_pt]
            exact heq_of_eq (hηg _ t hadm).symm
          rw [e2] at e1
          simp only [ModuliPackage.GPoint.map] at e1
          injection e1 with el ep
          have hab : g.comp (((IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))).comp (frobTwist Onr Fr (-((1 : ℕ) : ℤ)) ψ)) : Onr →+* (Localization.Away (f i))) = (algebraMap B L).comp ((Ξ B ψ hBπ ⟨E, ρ⟩).ψ : Onr →+* B) := by
            have := congrArg (fun (φ : Onr →ₐ[𝒪] L) => (φ : Onr →+* L)) el
            exact this.symm
          exact eq_of_heq ((hηc _ _ hab hL _ (t.map g)).symm.trans ep.symm)
        ·
          have e1 : (Ξ B (frobTwist Onr Fr (-1) ψ) hBπ ⟨E, ρp⟩).map (IsScalarTower.toAlgHom 𝒪 B L) = ((Ξ B (frobTwist Onr Fr (-1) ψ) hBπ ⟨E, ρp⟩).map (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i)))).map gO := by
            rw [hgO, ModuliPackage.GPoint.map_comp]
          rw [hmx'] at e1
          have e2 : ((⟨((IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))).comp (frobTwist Onr Fr (-((0 : ℕ) : ℤ)) (frobTwist Onr Fr (-1) ψ))), hL₀, η (Localization.Away (f i)) _ hL₀ t'⟩ : ModuliPackage.GPoint 𝒪 M (Localization.Away (f i))).map gO) =
              ⟨gO.comp ((IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))).comp (frobTwist Onr Fr (-((0 : ℕ) : ℤ)) (frobTwist Onr Fr (-1) ψ))), by simpa only [map_natCast] using hBr.map (algebraMap B L),
                η L (g.comp (((IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))).comp (frobTwist Onr Fr (-((0 : ℕ) : ℤ)) (frobTwist Onr Fr (-1) ψ))) : Onr →+* (Localization.Away (f i)))) hL (t'.map g)⟩ := by
            refine ModuliPackage.GPoint.ext' ?_ ?_
            · rfl
            simp only [ModuliPackage.GPoint.map_pt]
            exact heq_of_eq (hηg _ t' hadm').symm
          rw [e2] at e1
          simp only [ModuliPackage.GPoint.map] at e1
          injection e1 with el ep
          have hab : g.comp (((IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))).comp (frobTwist Onr Fr (-((0 : ℕ) : ℤ)) (frobTwist Onr Fr (-1) ψ))) : Onr →+* (Localization.Away (f i))) = (algebraMap B L).comp ((Ξ B (frobTwist Onr Fr (-1) ψ) hBπ ⟨E, ρp⟩).ψ : Onr →+* B) := by
            have := congrArg (fun (φ : Onr →ₐ[𝒪] L) => (φ : Onr →+* L)) el
            exact this.symm
          exact eq_of_heq ((hηc _ _ hab hL _ (t'.map g)).symm.trans ep.symm)
        · have hT := CerednikDrinfeld.SpecialFormal.Rigidified.IsTranslate.map_ringHom_of_constantCoeff_eq_zero (Series.id _) (1 - 1) 0 _ g t t' hadm.2.2.1.1.1 hadm'.2.2.1.1.1 (fun i => MvPowerSeries.constantCoeff_X i) htr0
          rw [← RingHom.comp_assoc, hg] at hT
          rw [hone, hlegx]
          exact hT

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isActBy_scalar_zpow_rigidifiedToG_frobTwist_neg_one_of_comp_verschiebung
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isActBy_scalar_zpow_rigidifiedToG_frobTwist_neg_one_of_comp_verschiebung (solution)
