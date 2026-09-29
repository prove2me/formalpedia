-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_isoVia_corr_inducing_of_iso_reduction_of_act_pow_comp_eq_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/5324c32a-f083-58ac-b523-45261aea7609

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_lev_of_exists_comp_eq_of_isPullback
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_lev_iff_exists_mapPt_eq_of_coprime
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_pushPt_act_eq_pushPt_act_of_sub_eq_smul_of_nsmulPt_eq_one
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_pushPt_act_natCast_eq_nsmulPt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isoVia_corr_inducing_of_iso_reduction_of_act_pow_comp_eq_of_isAlgClosed

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.FormalOmega CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

namespace FcIsoUp

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

theorem mul_val_congr {S : Type} [CommRing S] (E : FakeEllipticCurve Λ N S) {T : Scheme.{0}}
    {t t' : T ⟶ Spec (CommRingCat.of S)} (e : t = t') (P Q : SchemeHomOver t E.f) (P' Q' : SchemeHomOver t' E.f)
    (hP : P.1 = P'.1) (hQ : Q.1 = Q'.1) : (E.L.mul t P Q).1 = (E.L.mul t' P' Q').1 := by
  subst e
  obtain rfl : P = P' := Subtype.ext hP
  obtain rfl : Q = Q' := Subtype.ext hQ
  rfl

theorem act_rpow_comp {S : Type} [CommRing S] (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (E : FakeEllipticCurve Λ N S) (r i j : ℕ) :
    E.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ E.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩ =
      E.act ⟨(((r ^ (i + j) : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
  have hmem : ((((r ^ j : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b]) * ((((r ^ i : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
    have := hΛℤ ((r ^ j : ℕ) * (r ^ i : ℕ) : ℤ)
    push_cast at this ⊢
    exact this
  rw [← E.act_mul _ _ hmem]
  congr 1
  apply Subtype.ext
  push_cast
  rw [← pow_add, Nat.add_comm]

theorem act_natCast_eq {S : Type} [CommRing S] (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (E : FakeEllipticCurve Λ N S) (n : ℕ) (h : (((n : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) :
    E.act ⟨((n : ℕ) : ℚ), h⟩ = E.act ⟨(((n : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
  congr 1 <;> (try (apply Subtype.ext; push_cast))

theorem natCast_mem (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (n : ℕ) : (((n : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
  have := hΛℤ (n : ℤ)
  push_cast at this
  exact this

theorem isNilpotent_nilEval {k B'' : Type} [CommRing k] [CommRing B''] [Algebra k B''] (n : ℕ)
    (φ : MvPowerSeries (Fin 2) k) (hφ : MvPowerSeries.constantCoeff φ = 0)
    (s : Fin 2 → B'') (hs : ∀ l, IsNilpotent (s l)) : IsNilpotent (MvFormalGroup.nilEval n φ s) := by
  classical
  rw [← mem_nilradical, ← Ideal.Quotient.eq_zero_iff_mem]
  unfold MvFormalGroup.nilEval
  have h1 := congrArg (fun F => F (MvPowerSeries.trunc' k (Finsupp.equivFunOnFinite.symm fun _ => n) φ))
    (MvPolynomial.comp_aeval (R := k) (f := s) (Ideal.Quotient.mkₐ k (nilradical B'')))
  simp only [AlgHom.comp_apply] at h1
  have h2 : (fun i => (Ideal.Quotient.mk (nilradical B'')) (s i)) = 0 :=
    funext fun l => Ideal.Quotient.eq_zero_iff_mem.mpr (mem_nilradical.mpr (hs l))
  rw [Ideal.Quotient.mkₐ_eq_mk] at h1
  rw [h1, h2, MvPolynomial.aeval_zero]
  have h3 : MvPolynomial.coeff 0 (MvPowerSeries.trunc' k (Finsupp.equivFunOnFinite.symm fun _ => n) φ) = 0 := by
    simp [MvPowerSeries.coeff_trunc', hφ]
  rw [MvPolynomial.constantCoeff_eq, h3, map_zero]

theorem nilEval_map {k K B'' : Type} [CommRing k] [CommRing K] [CommRing B''] [Algebra k K] [Algebra K B''] [Algebra k B'']
    [IsScalarTower k K B''] (n : ℕ) (φ : MvPowerSeries (Fin 2) k) (s : Fin 2 → B'') :
    MvFormalGroup.nilEval n (MvPowerSeries.map (algebraMap k K) φ) s = MvFormalGroup.nilEval n φ s := by
  classical
  unfold MvFormalGroup.nilEval
  rw [MvPowerSeries.trunc'_map, MvPolynomial.aeval_map_algebraMap]

theorem factorsThrough_congr {R : Type} [CommRing R] {A C : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (lev : C ⟶ A)
    {T : Scheme.{0}} {t t' : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f) (Q : SchemeHomOver t' f)
    (h : P.1 = Q.1) : FactorsThrough lev P ↔ FactorsThrough lev Q :=
  ⟨fun ⟨c, hc⟩ => ⟨c, hc.trans h⟩, fun ⟨c, hc⟩ => ⟨c, hc.trans h.symm⟩⟩

end FcIsoUp

theorem solution
    {r N : ℕ} [Fact r.Prime] [NeZero N] (hrN : ¬ r ∣ N)
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))

    (k : Type) [Field k] [IsAlgClosed k] [Algebra 𝒪 k] (hk : IsNilpotent (algebraMap 𝒪 k π)) (hkr : IsNilpotent ((r : ℕ) : k))
    (ψ : Onr →ₐ[𝒪] k)
    (x x' : FakeEllipticCurve.RigidifiedCurve r π A₀ k ψ)
    (X X' : FormalODModule r k)
    (θ : RelativeGroupLaw.FormalCoordinates x.1.f 2) (θ' : RelativeGroupLaw.FormalCoordinates x'.1.f 2)
    (hX : x.1.IsFormalModuleVia coord X θ) (hX' : x'.1.IsFormalModuleVia coord X' θ')
    (T₀ : FormalODModule.Hom X X')

    (θE : RelativeGroupLaw.FormalCoordinates x.2.Eb.f 2) (θE' : RelativeGroupLaw.FormalCoordinates x'.2.Eb.f 2)
    (hθE : x.2.Eb.IsFormalModuleVia coord (X.map (algebraMap k (k ⧸ Ideal.span {algebraMap 𝒪 k π}))) θE)
    (hθE' : x'.2.Eb.IsFormalModuleVia coord (X'.map (algebraMap k (k ⧸ Ideal.span {algebraMap 𝒪 k π}))) θE')
    (hθEg : ∀ (B'' : Type) [CommRing B''] [Algebra k B''] [Algebra (k ⧸ Ideal.span {algebraMap 𝒪 k π}) B'']
      [IsScalarTower k (k ⧸ Ideal.span {algebraMap 𝒪 k π}) B''] (s : Fin 2 → B''),
      (∀ i, IsNilpotent (s i)) → (θE B'' s).1 ≫ x.2.gb = (θ B'' s).1)
    (hθEg' : ∀ (B'' : Type) [CommRing B''] [Algebra k B''] [Algebra (k ⧸ Ideal.span {algebraMap 𝒪 k π}) B'']
      [IsScalarTower k (k ⧸ Ideal.span {algebraMap 𝒪 k π}) B''] (s : Fin 2 → B''),
      (∀ i, IsNilpotent (s i)) → (θE' B'' s).1 ≫ x'.2.gb = (θ' B'' s).1)

    (uA : x'.2.Ab.A ⟶ x.2.Ab.A) (huA : FakeEllipticCurve.IsPullbackVia (RingHom.id _) x.2.Ab x'.2.Ab uA) (huAg : uA ≫ x.2.gA = x'.2.gA)
    (v : x.2.Ab.A ⟶ x'.2.Ab.A) (hv : FakeEllipticCurve.IsPullbackVia (RingHom.id _) x'.2.Ab x.2.Ab v) (hvg : v ≫ x'.2.gA = x.2.gA)
    (huv : uA ≫ v = 𝟙 _) (hvu : v ≫ uA = 𝟙 _)

    (c₀ c c' : ℕ)
    (e : x.2.Eb.A ≅ x'.2.Eb.A) (he : e.hom ≫ x'.2.Eb.f = x.2.Eb.f)
    (hαe : (x.2.Ab.act ⟨(((r ^ c₀ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ x.2.φ' ≫ x.2.Eb.act ⟨(((r ^ c : ℕ) : ℤ) : ℚ), hΛℤ _⟩) ≫ e.hom =
      x.2.Ab.act ⟨(((r ^ c₀ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ v ≫ x'.2.φ' ≫ x'.2.Eb.act ⟨(((r ^ c' : ℕ) : ℤ) : ℚ), hΛℤ _⟩)
    (hemul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (k ⧸ Ideal.span {algebraMap 𝒪 k π}))) (P Q : SchemeHomOver t x.2.Eb.f),
      mapPt e.hom he (x.2.Eb.L.mul t P Q) = x'.2.Eb.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q))
    (heact : ∀ y : ↥Λ, x.2.Eb.act y ≫ e.hom = e.hom ≫ x'.2.Eb.act y)
    (heT : ∀ (B'' : Type) [CommRing B''] [Algebra (k ⧸ Ideal.span {algebraMap 𝒪 k π}) B''] (J : Ideal B'') (n : ℕ), J ^ (n + 1) = ⊥ →
      ∀ s : Fin 2 → B'', (∀ l, s l ∈ J) →
        (θE B'' s).1 ≫ e.hom =
          (θE' B'' (fun l => MvFormalGroup.nilEval n ((T₀.toSeries.map (algebraMap k (k ⧸ Ideal.span {algebraMap 𝒪 k π}))) l) s)).1) :
    ∃ (i : x.1.A ≅ x'.1.A) (hi : i.hom ≫ x'.1.f = x.1.f), FakeEllipticCurve.IsoVia x.1 x'.1 i hi ∧

      (∀ (B'' : Type) [CommRing B''] [Algebra k B''] (J : Ideal B'') (n : ℕ), J ^ (n + 1) = ⊥ →
          ∀ s : Fin 2 → B'', (∀ l, s l ∈ J) →
            (θ B'' s).1 ≫ i.hom = (θ' B'' (fun l => MvFormalGroup.nilEval n (T₀.toSeries l) s)).1) ∧

      ∃ (ib : x.2.Eb.A ⟶ x'.2.Eb.A) (_ : ib ≫ x'.2.gb = x.2.gb ≫ i.hom) (_ : ib ≫ x'.2.Eb.f = x.2.Eb.f)
        (uA : x'.2.Ab.A ⟶ x.2.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) x.2.Ab x'.2.Ab uA) (_ : uA ≫ x.2.gA = x'.2.gA)
        (i₁ j₁ : ℕ),
        ib ≫ x'.2.φ ≫ uA ≫ x.2.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = x.2.φ ≫ x.2.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
  classical
  obtain ⟨E, ρ⟩ := x
  obtain ⟨E', ρ'⟩ := x'
  simp only at *

  have hπ0 : algebraMap 𝒪 k π = 0 := hk.eq_zero
  have hIbot : Ideal.span {algebraMap 𝒪 k π} = ⊥ := by rw [hπ0, Ideal.span_singleton_eq_bot]
  have hmk : Function.Bijective (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 k π})) :=
    ⟨(RingHom.injective_iff_ker_eq_bot _).mpr (by rw [Ideal.mk_ker, hIbot]), Ideal.Quotient.mk_surjective⟩
  let emk : k ≃+* (k ⧸ Ideal.span {algebraMap 𝒪 k π}) := RingEquiv.ofBijective _ hmk
  haveI hSpecIso : IsIso (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 k π})))) := by
    haveI : IsIso (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 k π}))) :=
      ⟨⟨CommRingCat.ofHom emk.symm.toRingHom,
        by ext1; apply RingHom.ext; intro y; exact emk.symm_apply_apply y,
        by ext1; apply RingHom.ext; intro y; exact emk.apply_symm_apply y⟩⟩
    infer_instance
  obtain ⟨hsq, gmul, gact, glev⟩ := id ρ.isPullback_Eb
  obtain ⟨hsq', gmul', gact', glev'⟩ := id ρ'.isPullback_Eb
  haveI : IsIso ρ.gb := hsq.isIso_fst_of_isIso
  haveI : IsIso ρ'.gb := hsq'.isIso_fst_of_isIso
  obtain ⟨hφo, hφ'o, hφmul, hφ'mul, hφlin, hφ'lin, hdeg⟩ := ρ.isIsogenyPair
  obtain ⟨hφo', hφ'o', hφmul', hφ'mul', hφlin', hφ'lin', hdeg'⟩ := ρ'.isIsogenyPair
  obtain ⟨huApb, huAmul, huAact, huAlev⟩ := id huA
  obtain ⟨hvpb, hvmul, hvact, hvlev⟩ := id hv
  have hm : ((((r ^ ρ.d : ℕ)) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := FcIsoUp.natCast_mem hΛℤ _
  have hm' : ((((r ^ ρ'.d : ℕ)) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := FcIsoUp.natCast_mem hΛℤ _
  have hd1 : ρ.φ ≫ ρ.φ' = ρ.Eb.act ⟨(((r ^ ρ.d : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
    rw [(hdeg hm).1, FcIsoUp.act_natCast_eq hΛℤ]
  have hd2 : ρ'.φ' ≫ ρ'.φ = ρ'.Ab.act ⟨(((r ^ ρ'.d : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
    rw [(hdeg' hm').2, FcIsoUp.act_natCast_eq hΛℤ]
  have hd1' : ρ'.φ ≫ ρ'.φ' = ρ'.Eb.act ⟨(((r ^ ρ'.d : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
    rw [(hdeg' hm').1, FcIsoUp.act_natCast_eq hΛℤ]
  have Lφ : ρ.φ ≫ ρ.Ab.act ⟨(((r ^ c₀ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ ρ.φ' ≫ ρ.Eb.act ⟨(((r ^ c : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ.Eb.act ⟨(((r ^ (c₀ + (ρ.d + c)) : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
    rw [reassoc_of% (hφlin ⟨(((r ^ c₀ : ℕ) : ℤ) : ℚ), hΛℤ _⟩).symm, reassoc_of% hd1,
      FcIsoUp.act_rpow_comp hΛℤ, FcIsoUp.act_rpow_comp hΛℤ]
  have Lφ' : ρ'.φ ≫ ρ'.Ab.act ⟨(((r ^ c₀ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ ρ'.φ' ≫ ρ'.Eb.act ⟨(((r ^ c' : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ'.Eb.act ⟨(((r ^ (c₀ + (ρ'.d + c')) : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
    rw [reassoc_of% (hφlin' ⟨(((r ^ c₀ : ℕ) : ℤ) : ℚ), hΛℤ _⟩).symm, reassoc_of% hd1',
      FcIsoUp.act_rpow_comp hΛℤ, FcIsoUp.act_rpow_comp hΛℤ]

  have hαe' : (ρ'.Ab.act ⟨(((r ^ c₀ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ ρ'.φ' ≫ ρ'.Eb.act ⟨(((r ^ c' : ℕ) : ℤ) : ℚ), hΛℤ _⟩) ≫ e.inv =
      uA ≫ ρ.Ab.act ⟨(((r ^ c₀ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ ρ.φ' ≫ ρ.Eb.act ⟨(((r ^ c : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
    have h0 : uA ≫ (ρ.Ab.act ⟨(((r ^ c₀ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ v ≫ ρ'.φ' ≫ ρ'.Eb.act ⟨(((r ^ c' : ℕ) : ℤ) : ℚ), hΛℤ _⟩) =
        ρ'.Ab.act ⟨(((r ^ c₀ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ ρ'.φ' ≫ ρ'.Eb.act ⟨(((r ^ c' : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
      rw [reassoc_of% (huAact ⟨(((r ^ c₀ : ℕ) : ℤ) : ℚ), hΛℤ _⟩).symm, reassoc_of% huv]
    rw [← h0, ← hαe]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hαe_r : ρ.Ab.act ⟨(((r ^ c₀ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ ρ.φ' ≫ ρ.Eb.act ⟨(((r ^ c : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ e.hom = ρ.Ab.act ⟨(((r ^ c₀ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ v ≫ ρ'.φ' ≫ ρ'.Eb.act ⟨(((r ^ c' : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
    simpa only [Category.assoc] using hαe
  have hEbf : inv ρ.gb ≫ ρ.Eb.f = E.f ≫ inv (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 k π})))) := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, hsq.w, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

  have hiE : (inv ρ.gb ≫ e.hom ≫ ρ'.gb) ≫ E'.f = E.f := by
    rw [Category.assoc, Category.assoc, hsq'.w, ← Category.assoc e.hom, he, ← hsq.w, IsIso.inv_hom_id_assoc]
  refine ⟨⟨inv ρ.gb ≫ e.hom ≫ ρ'.gb, inv ρ'.gb ≫ e.inv ≫ ρ.gb, ?_, ?_⟩, hiE, ⟨?_, ?_, ?_⟩, ?_,
    e.hom, ?_, he, uA, huA, huAg, c₀ + (ρ.d + c), c₀ + (ρ'.d + c'), ?_⟩
  · simp only [Category.assoc, IsIso.hom_inv_id_assoc, Iso.hom_inv_id_assoc, IsIso.inv_hom_id]
  · simp only [Category.assoc, IsIso.hom_inv_id_assoc, Iso.inv_hom_id_assoc, IsIso.inv_hom_id]
  ·
    intro T t P Q
    apply Subtype.ext
    simp only [mapPt_coe]
    set tb := t ≫ inv (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 k π})))) with htb
    have htb' : tb ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 k π}))) = t := by
      rw [htb, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    let Pb : SchemeHomOver tb ρ.Eb.f := ⟨P.1 ≫ inv ρ.gb, by rw [Category.assoc, hEbf, ← Category.assoc, P.2]⟩
    let Qb : SchemeHomOver tb ρ.Eb.f := ⟨Q.1 ≫ inv ρ.gb, by rw [Category.assoc, hEbf, ← Category.assoc, Q.2]⟩
    have s1 : (E.L.mul t P Q).1 ≫ inv ρ.gb = (ρ.Eb.L.mul tb Pb Qb).1 := by
      rw [IsIso.comp_inv_eq, gmul]
      exact FcIsoUp.mul_val_congr E htb'.symm _ _ _ _ (by simp [Pb]) (by simp [Qb])
    have s2 : (ρ.Eb.L.mul tb Pb Qb).1 ≫ e.hom = (ρ'.Eb.L.mul tb (mapPt e.hom he Pb) (mapPt e.hom he Qb)).1 := by
      have := congrArg Subtype.val (hemul tb Pb Qb)
      simpa only [mapPt_coe] using this
    have s3 : (ρ'.Eb.L.mul tb (mapPt e.hom he Pb) (mapPt e.hom he Qb)).1 ≫ ρ'.gb =
        (E'.L.mul t ⟨P.1 ≫ inv ρ.gb ≫ e.hom ≫ ρ'.gb, by rw [Category.assoc, hiE, P.2]⟩
          ⟨Q.1 ≫ inv ρ.gb ≫ e.hom ≫ ρ'.gb, by rw [Category.assoc, hiE, Q.2]⟩).1 := by
      rw [gmul']
      exact FcIsoUp.mul_val_congr E' htb' _ _ _ _ (by simp [Pb, mapPt_coe]) (by simp [Qb, mapPt_coe])
    rw [← Category.assoc, s1, ← Category.assoc, s2, s3]
    rfl
  ·
    intro y
    have h1 : E.act y ≫ inv ρ.gb = inv ρ.gb ≫ ρ.Eb.act y := by
      rw [IsIso.eq_inv_comp, ← Category.assoc, ← gact, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    simp only []
    rw [← Category.assoc, h1, Category.assoc, Category.assoc, Category.assoc, ← Category.assoc (ρ.Eb.act y), heact,
      Category.assoc, gact']
  ·
    intro T t P

    have hcop : ∀ m : ℕ, IsCoprime ((r ^ m : ℕ) : ℤ) (N : ℤ) := fun m =>
      Nat.isCoprime_iff_coprime.mpr (Nat.Coprime.pow_left m ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hrN))
    have h1Λ : (1 : ℍ[ℚ, a, b]) ∈ Λ := by have := hΛℤ 1; push_cast at this; exact this

    have hlevφ' : ∀ {T : Scheme.{0}} (tt : T ⟶ Spec (CommRingCat.of (k ⧸ Ideal.span {algebraMap 𝒪 k π}))) (Q : SchemeHomOver tt ρ.Ab.f),
        FactorsThrough ρ.Ab.lev Q → FactorsThrough ρ.Eb.lev (mapPt ρ.φ' hφ'o Q) := by
      intro T tt Q hQ
      have hm : ((((r ^ ρ.d : ℕ)) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := FcIsoUp.natCast_mem hΛℤ _
      have key := FakeEllipticCurve.factorsThrough_lev_iff_exists_mapPt_eq_of_coprime ρ.Eb ρ.Ab ρ.φ hφo hφmul ρ.φ' hφ'o
        (r ^ ρ.d) (Nat.Coprime.pow_left ρ.d ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hrN))
        (fun tt P => by
          rw [← FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt ρ.Eb h1Λ (r ^ ρ.d) hm]
          apply Subtype.ext
          simp only [mapPt_coe, pushPt, Category.assoc, (hdeg hm).1])
        ρ.preservesLevel tt Q
      obtain ⟨P₁, hP₁, rfl⟩ := key.mp hQ
      rw [show mapPt ρ.φ' hφ'o (mapPt ρ.φ hφo P₁) = pushPt (ρ.Eb.act ⟨(((r ^ ρ.d : ℕ) : ℤ) : ℚ), hΛℤ _⟩) (ρ.Eb.act_over _) P₁ from
        Subtype.ext (by simp only [mapPt_coe, pushPt, Category.assoc, (hdeg hm).1, FcIsoUp.act_natCast_eq hΛℤ])]
      exact ρ.Eb.lev_stable _ tt P₁ hP₁
    have hlevφ'' : ∀ {T : Scheme.{0}} (tt : T ⟶ Spec (CommRingCat.of (k ⧸ Ideal.span {algebraMap 𝒪 k π}))) (Q : SchemeHomOver tt ρ'.Ab.f),
        FactorsThrough ρ'.Ab.lev Q → FactorsThrough ρ'.Eb.lev (mapPt ρ'.φ' hφ'o' Q) := by
      intro T tt Q hQ
      have hm : ((((r ^ ρ'.d : ℕ)) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := FcIsoUp.natCast_mem hΛℤ _
      have key := FakeEllipticCurve.factorsThrough_lev_iff_exists_mapPt_eq_of_coprime ρ'.Eb ρ'.Ab ρ'.φ hφo' hφmul' ρ'.φ' hφ'o'
        (r ^ ρ'.d) (Nat.Coprime.pow_left ρ'.d ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hrN))
        (fun tt P => by
          rw [← FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt ρ'.Eb h1Λ (r ^ ρ'.d) hm]
          apply Subtype.ext
          simp only [mapPt_coe, pushPt, Category.assoc, (hdeg' hm).1])
        ρ'.preservesLevel tt Q
      obtain ⟨P₁, hP₁, rfl⟩ := key.mp hQ
      rw [show mapPt ρ'.φ' hφ'o' (mapPt ρ'.φ hφo' P₁) = pushPt (ρ'.Eb.act ⟨(((r ^ ρ'.d : ℕ) : ℤ) : ℚ), hΛℤ _⟩) (ρ'.Eb.act_over _) P₁ from
        Subtype.ext (by simp only [mapPt_coe, pushPt, Category.assoc, (hdeg' hm).1, FcIsoUp.act_natCast_eq hΛℤ])]
      exact ρ'.Eb.lev_stable _ tt P₁ hP₁

    have hfix : ∀ (F : FakeEllipticCurve Λ N (k ⧸ Ideal.span {algebraMap 𝒪 k π})) {T : Scheme.{0}} (tt : T ⟶ Spec (CommRingCat.of (k ⧸ Ideal.span {algebraMap 𝒪 k π})))
        (P₁ : SchemeHomOver tt F.f), FactorsThrough F.lev P₁ → ∀ m : ℕ,
        P₁.1 ≫ F.act ⟨((Int.gcdA ((r ^ m : ℕ) : ℤ) N : ℤ) : ℚ), hΛℤ _⟩ ≫ F.act ⟨(((r ^ m : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = P₁.1 := by
      intro F T tt P₁ hP₁ m
      have hb := Int.gcd_eq_gcd_ab ((r ^ m : ℕ) : ℤ) N
      rw [Int.gcd_natCast_natCast, Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left m ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hrN))] at hb
      have hmem : (((((r ^ m : ℕ) : ℤ)) : ℚ) : ℍ[ℚ, a, b]) * ((((Int.gcdA ((r ^ m : ℕ) : ℤ) N) : ℤ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
        have := hΛℤ (((r ^ m : ℕ) : ℤ) * Int.gcdA ((r ^ m : ℕ) : ℤ) N); push_cast at this ⊢; exact this
      have hq : (((r ^ m : ℕ) : ℤ) : ℚ) * ((Int.gcdA ((r ^ m : ℕ) : ℤ) N : ℤ) : ℚ) - 1 =
          (N : ℚ) * (((-Int.gcdB ((r ^ m : ℕ) : ℤ) N) : ℤ) : ℚ) := by
        have hb' := congrArg (Int.cast : ℤ → ℚ) hb
        push_cast at hb' ⊢
        linarith
      have step := FakeEllipticCurve.pushPt_act_eq_pushPt_act_of_sub_eq_smul_of_nsmulPt_eq_one F h1Λ N tt P₁ (F.lev_torsion tt P₁ hP₁)
        ⟨_, hmem⟩ ⟨1, h1Λ⟩ ⟨⟨(((-Int.gcdB ((r ^ m : ℕ) : ℤ) N) : ℤ) : ℚ), hΛℤ _⟩, by
          rw [QuaternionAlgebra.smul_coe]
          simp only [Submodule.coe_mk]
          exact_mod_cast congrArg (fun q : ℚ => (q : ℍ[ℚ, a, b])) hq⟩
      have hv := congrArg Subtype.val step
      simp only [pushPt, mapPt_coe] at hv
      rw [F.act_mul ⟨(((r ^ m : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ⟨((Int.gcdA ((r ^ m : ℕ) : ℤ) N : ℤ) : ℚ), hΛℤ _⟩ hmem, F.act_one h1Λ,
        Category.comp_id] at hv
      simpa only [Category.assoc] using hv
    set tb := t ≫ inv (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 k π})))) with htb
    let Pb : SchemeHomOver tb ρ.Eb.f := ⟨P.1 ≫ inv ρ.gb, by rw [Category.assoc, hEbf, ← Category.assoc, P.2]⟩

    have iffa : FactorsThrough E.lev P ↔ FactorsThrough ρ.Eb.lev Pb := by
      constructor
      · rintro ⟨c₁, hc₁⟩
        exact FakeEllipticCurve.factorsThrough_lev_of_exists_comp_eq_of_isPullback _ E ρ.Eb ρ.gb hsq gmul glev tb Pb
          ⟨c₁, by rw [hc₁]; simp [Pb]⟩
      · intro h
        obtain ⟨P₀, hP₀⟩ := glev tb Pb h
        exact ⟨P₀, by rw [hP₀]; simp [Pb]⟩

    have iffc : FactorsThrough ρ'.Eb.lev (mapPt e.hom he Pb) ↔
        FactorsThrough E'.lev (mapPt (inv ρ.gb ≫ e.hom ≫ ρ'.gb) hiE P) := by
      constructor
      · intro h
        obtain ⟨P₀, hP₀⟩ := glev' tb (mapPt e.hom he Pb) h
        exact ⟨P₀, by rw [hP₀]; simp [Pb, mapPt_coe]⟩
      · rintro ⟨c₁, hc₁⟩
        exact FakeEllipticCurve.factorsThrough_lev_of_exists_comp_eq_of_isPullback _ E' ρ'.Eb ρ'.gb hsq' gmul' glev' tb
          (mapPt e.hom he Pb) ⟨c₁, by rw [hc₁]; simp [Pb, mapPt_coe]⟩

    have hvf : v ≫ ρ'.Ab.f = ρ.Ab.f := by
      have := hvpb.w; simpa only [CommRingCat.ofHom_id, Spec.map_id, Category.comp_id] using this
    have huf : uA ≫ ρ.Ab.f = ρ'.Ab.f := by
      have := huApb.w; simpa only [CommRingCat.ofHom_id, Spec.map_id, Category.comp_id] using this
    have iffb : FactorsThrough ρ.Eb.lev Pb ↔ FactorsThrough ρ'.Eb.lev (mapPt e.hom he Pb) := by
      constructor
      · intro hPb
        have hfx := hfix ρ.Eb tb Pb hPb (c₀ + (ρ.d + c))
        let R₁ := pushPt (ρ.Eb.act ⟨((Int.gcdA ((r ^ (c₀ + (ρ.d + c)) : ℕ) : ℤ) N : ℤ) : ℚ), hΛℤ _⟩) (ρ.Eb.act_over _) Pb
        have hR₁ : FactorsThrough ρ.Eb.lev R₁ := ρ.Eb.lev_stable _ tb Pb hPb
        let R₂ := mapPt ρ.φ hφo R₁
        have hR₂ : FactorsThrough ρ.Ab.lev R₂ := ρ.preservesLevel tb R₁ hR₁
        let R₃ := pushPt (ρ.Ab.act ⟨(((r ^ c₀ : ℕ) : ℤ) : ℚ), hΛℤ _⟩) (ρ.Ab.act_over _) R₂
        have hR₃ : FactorsThrough ρ.Ab.lev R₃ := ρ.Ab.lev_stable _ tb R₂ hR₂
        let R₄ : SchemeHomOver tb ρ'.Ab.f := ⟨R₃.1 ≫ v, by rw [Category.assoc, hvf, R₃.2]⟩
        have hR₄ : FactorsThrough ρ'.Ab.lev R₄ := by
          obtain ⟨P₀, hP₀⟩ := hvlev tb R₃ hR₃
          exact ⟨P₀, hP₀⟩
        let R₅ := mapPt ρ'.φ' hφ'o' R₄
        have hR₅ : FactorsThrough ρ'.Eb.lev R₅ := hlevφ'' tb R₄ hR₄
        let R₆ := pushPt (ρ'.Eb.act ⟨(((r ^ c' : ℕ) : ℤ) : ℚ), hΛℤ _⟩) (ρ'.Eb.act_over _) R₅
        have hR₆ : FactorsThrough ρ'.Eb.lev R₆ := ρ'.Eb.lev_stable _ tb R₅ hR₅
        refine (FcIsoUp.factorsThrough_congr _ (mapPt e.hom he Pb) R₆ ?_).mpr hR₆
        have hR6 : R₆.1 = Pb.1 ≫ ρ.Eb.act ⟨((Int.gcdA ((r ^ (c₀ + (ρ.d + c)) : ℕ) : ℤ) N : ℤ) : ℚ), hΛℤ _⟩ ≫ ρ.φ ≫ ρ.Ab.act ⟨(((r ^ c₀ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ v ≫ ρ'.φ' ≫ ρ'.Eb.act ⟨(((r ^ c' : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
          simp only [R₆, R₅, R₄, R₃, R₂, R₁, mapPt_coe, pushPt, Category.assoc]
        rw [mapPt_coe, hR6, ← hαe_r, reassoc_of% Lφ, reassoc_of% hfx]
      · intro hQ
        have hfx := hfix ρ'.Eb tb (mapPt e.hom he Pb) hQ (c₀ + (ρ'.d + c'))
        let R₁ := pushPt (ρ'.Eb.act ⟨((Int.gcdA ((r ^ (c₀ + (ρ'.d + c')) : ℕ) : ℤ) N : ℤ) : ℚ), hΛℤ _⟩) (ρ'.Eb.act_over _) (mapPt e.hom he Pb)
        have hR₁ : FactorsThrough ρ'.Eb.lev R₁ := ρ'.Eb.lev_stable _ tb _ hQ
        let R₂ := mapPt ρ'.φ hφo' R₁
        have hR₂ : FactorsThrough ρ'.Ab.lev R₂ := ρ'.preservesLevel tb R₁ hR₁
        let R₃ : SchemeHomOver tb ρ.Ab.f := ⟨R₂.1 ≫ uA, by rw [Category.assoc, huf, R₂.2]⟩
        have hR₃ : FactorsThrough ρ.Ab.lev R₃ := by
          obtain ⟨P₀, hP₀⟩ := huAlev tb R₂ hR₂
          exact ⟨P₀, hP₀⟩
        let R₄ := pushPt (ρ.Ab.act ⟨(((r ^ c₀ : ℕ) : ℤ) : ℚ), hΛℤ _⟩) (ρ.Ab.act_over _) R₃
        have hR₄ : FactorsThrough ρ.Ab.lev R₄ := ρ.Ab.lev_stable _ tb R₃ hR₃
        let R₅ := mapPt ρ.φ' hφ'o R₄
        have hR₅ : FactorsThrough ρ.Eb.lev R₅ := hlevφ' tb R₄ hR₄
        let R₆ := pushPt (ρ.Eb.act ⟨(((r ^ c : ℕ) : ℤ) : ℚ), hΛℤ _⟩) (ρ.Eb.act_over _) R₅
        have hR₆ : FactorsThrough ρ.Eb.lev R₆ := ρ.Eb.lev_stable _ tb R₅ hR₅
        refine (FcIsoUp.factorsThrough_congr _ Pb R₆ ?_).mpr hR₆
        have hR6 : R₆.1 = Pb.1 ≫ e.hom ≫ ρ'.Eb.act ⟨((Int.gcdA ((r ^ (c₀ + (ρ'.d + c')) : ℕ) : ℤ) N : ℤ) : ℚ), hΛℤ _⟩ ≫ ρ'.φ ≫ uA ≫ ρ.Ab.act ⟨(((r ^ c₀ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ ρ.φ' ≫ ρ.Eb.act ⟨(((r ^ c : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
          simp only [R₆, R₅, R₄, R₃, R₂, R₁, mapPt_coe, pushPt, Category.assoc]
        rw [mapPt_coe] at hfx
        rw [hR6, ← hαe']
        simp only [Category.assoc]
        rw [reassoc_of% Lφ', reassoc_of% hfx, Iso.hom_inv_id, Category.comp_id]
    exact iffa.trans (iffb.trans iffc)
  ·
    intro B'' _ _ J n hJ s hs
    have hker : ∀ y ∈ Ideal.span {algebraMap 𝒪 k π}, algebraMap k B'' y = 0 := by
      intro y hy
      rw [hIbot] at hy
      rw [(Submodule.mem_bot k).mp hy, map_zero]
    letI algq : Algebra (k ⧸ Ideal.span {algebraMap 𝒪 k π}) B'' := (Ideal.Quotient.lift (Ideal.span {algebraMap 𝒪 k π}) (algebraMap k B'') hker).toAlgebra
    haveI : IsScalarTower k (k ⧸ Ideal.span {algebraMap 𝒪 k π}) B'' :=
      IsScalarTower.of_algebraMap_eq (fun y => (Ideal.Quotient.lift_mk (Ideal.span {algebraMap 𝒪 k π}) (algebraMap k B'') hker).symm)
    have hsn : ∀ l, IsNilpotent (s l) := fun l =>
      ⟨n + 1, by have h := Ideal.pow_mem_pow (hs l) (n + 1); rw [hJ] at h; exact (Submodule.mem_bot _).mp h⟩
    have hs'n : ∀ l, IsNilpotent (MvFormalGroup.nilEval n (T₀.toSeries l) s) := fun l =>
      FcIsoUp.isNilpotent_nilEval n _ (T₀.isODHom.constantCoeff l) s hsn
    have e1 := hθEg B'' s hsn
    have e2 := heT B'' J n hJ s hs
    have e3 := hθEg' B'' (fun l => MvFormalGroup.nilEval n (T₀.toSeries l) s) hs'n
    have hmapEq : (fun l => MvFormalGroup.nilEval n ((T₀.toSeries.map (algebraMap k (k ⧸ Ideal.span {algebraMap 𝒪 k π}))) l) s) =
        fun l => MvFormalGroup.nilEval n (T₀.toSeries l) s := by
      funext l
      exact FcIsoUp.nilEval_map n (T₀.toSeries l) s
    rw [hmapEq] at e2
    simp only []
    rw [← e1, Category.assoc, IsIso.hom_inv_id_assoc, reassoc_of% e2, e3]
  ·
    simp only [IsIso.hom_inv_id_assoc]
  ·
    have L1 : ρ.φ ≫ ρ.Ab.act ⟨(((r ^ c₀ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ ρ.φ' ≫ ρ.Eb.act ⟨(((r ^ c : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ e.hom ≫ ρ'.φ ≫ uA =
        e.hom ≫ ρ'.φ ≫ uA ≫ ρ.Ab.act ⟨(((r ^ (c₀ + (ρ.d + c)) : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
      rw [reassoc_of% (hφlin ⟨(((r ^ c₀ : ℕ) : ℤ) : ℚ), hΛℤ _⟩).symm, reassoc_of% hd1,
        reassoc_of% (FcIsoUp.act_rpow_comp hΛℤ ρ.Eb r ρ.d c),
        reassoc_of% (FcIsoUp.act_rpow_comp hΛℤ ρ.Eb r c₀ (ρ.d + c)),
        reassoc_of% (heact ⟨(((r ^ (c₀ + (ρ.d + c)) : ℕ) : ℤ) : ℚ), hΛℤ _⟩),
        reassoc_of% (hφlin' ⟨(((r ^ (c₀ + (ρ.d + c)) : ℕ) : ℤ) : ℚ), hΛℤ _⟩), huAact]
    have L2 : ρ.φ ≫ ρ.Ab.act ⟨(((r ^ c₀ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ v ≫ ρ'.φ' ≫ ρ'.Eb.act ⟨(((r ^ c' : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ ρ'.φ ≫ uA =
        ρ.φ ≫ ρ.Ab.act ⟨(((r ^ (c₀ + (ρ'.d + c')) : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
      rw [reassoc_of% (hφlin' ⟨(((r ^ c' : ℕ) : ℤ) : ℚ), hΛℤ _⟩), reassoc_of% hd2,
        reassoc_of% (FcIsoUp.act_rpow_comp hΛℤ ρ'.Ab r ρ'.d c'), huAact, reassoc_of% hvu,
        FcIsoUp.act_rpow_comp hΛℤ]
    have key : ρ.φ ≫ ((ρ.Ab.act ⟨(((r ^ c₀ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ ρ.φ' ≫ ρ.Eb.act ⟨(((r ^ c : ℕ) : ℤ) : ℚ), hΛℤ _⟩) ≫ e.hom) ≫ ρ'.φ ≫ uA =
        ρ.φ ≫ (ρ.Ab.act ⟨(((r ^ c₀ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ v ≫ ρ'.φ' ≫ ρ'.Eb.act ⟨(((r ^ c' : ℕ) : ℤ) : ℚ), hΛℤ _⟩) ≫ ρ'.φ ≫ uA := by rw [hαe]
    simp only [Category.assoc] at key
    rw [L1, L2] at key
    exact key

end S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isoVia_corr_inducing_of_iso_reduction_of_act_pow_comp_eq_of_isAlgClosed
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isoVia_corr_inducing_of_iso_reduction_of_act_pow_comp_eq_of_isAlgClosed (solution)
