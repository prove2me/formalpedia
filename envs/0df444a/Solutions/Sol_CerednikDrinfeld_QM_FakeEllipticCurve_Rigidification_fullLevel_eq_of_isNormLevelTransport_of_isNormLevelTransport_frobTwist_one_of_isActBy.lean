-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.fullLevel_eq_of_isNormLevelTransport_of_isNormLevelTransport_frobTwist_one_of_isActBy
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/6ebba517-2043-54b3-90bf-b50942158119

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_QMRigidificationLevel
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_n_eq_of_isRigTransport_of_isRigTransport_frobTwist_one_of_isActBy
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_eq_of_specMap_comp_eq_of_nsmulPt_eq_one_of_isNilpotent_ker
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_comp_eq_and_comp_eq_nsmulPt_of_frobTwist_one_sections
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_fullLevel_eq_of_isNormLevelTransport_of_isNormLevelTransport_frobTwist_one_of_isActBy
p2m_attr_erase "instance" "MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
p2m_open "CategoryTheory AlgebraicGeometry QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.FormalOmega CerednikDrinfeld.SpecialFormal NeronModelInfra~schemeHomOverComp GoodReductionJacobian"

namespace TRNpAsm

open CerednikDrinfeld.QM.FakeEllipticCurve

section Square

variable {S S' : Type} [CommRing S] [CommRing S'] {φ : S →+* S'}
variable {A A' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} {f' : A' ⟶ Spec (CommRingCat.of S')} {g : A' ⟶ A}

def img (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ))) {T : Scheme.{0}}
    {t' : T ⟶ Spec (CommRingCat.of S')} (P : SchemeHomOver t' f') :
    SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom φ)) f :=
  ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩

@[scoped simp] theorem img_coe (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ))) {T : Scheme.{0}}
    {t' : T ⟶ Spec (CommRingCat.of S')} (P : SchemeHomOver t' f') : (img hg P).1 = P.1 ≫ g := rfl

theorem img_injective (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ))) {T : Scheme.{0}}
    {t' : T ⟶ Spec (CommRingCat.of S')} {P Q : SchemeHomOver t' f'} (h : img hg P = img hg Q) : P = Q := by
  apply Subtype.ext
  apply hg.hom_ext
  · exact congrArg Subtype.val h
  · rw [P.2, Q.2]

theorem img_one (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
    (L : RelativeGroupLaw S f) (L' : RelativeGroupLaw S' f')
    (hg_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' f'),
      (L'.mul t' P Q).1 ≫ g = (L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ)) (img hg P) (img hg Q)).1)
    {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) :
    img hg (L'.one t') = L.one (t' ≫ Spec.map (CommRingCat.ofHom φ)) := by
  set x := img hg (L'.one t') with hx
  have hxx : L.mul _ x x = x := by
    apply Subtype.ext
    rw [hx, ← hg_mul, L'.one_mul]
    rfl
  letI := L.pointGroup (t' ≫ Spec.map (CommRingCat.ofHom φ))
  have h2 : x * x = x * 1 := by rw [mul_one]; exact hxx
  exact mul_left_cancel h2

theorem img_mul (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
    (L : RelativeGroupLaw S f) (L' : RelativeGroupLaw S' f')
    (hg_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' f'),
      (L'.mul t' P Q).1 ≫ g = (L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ)) (img hg P) (img hg Q)).1)
    {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' f') :
    img hg (L'.mul t' P Q) = L.mul _ (img hg P) (img hg Q) :=
  Subtype.ext (hg_mul t' P Q)

theorem img_pushPt (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
    (e : A ⟶ A) (he : e ≫ f = f) (e' : A' ⟶ A') (he' : e' ≫ f' = f') (hcomm : e' ≫ g = g ≫ e)
    {T : Scheme.{0}} {t' : T ⟶ Spec (CommRingCat.of S')} (P : SchemeHomOver t' f') :
    img hg (pushPt e' he' P) = pushPt e he (img hg P) := by
  apply Subtype.ext
  simp only [img_coe, pushPt, mapPt_coe, Category.assoc, hcomm]

theorem img_pow (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
    (L : RelativeGroupLaw S f) (L' : RelativeGroupLaw S' f')
    (hg_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' f'),
      (L'.mul t' P Q).1 ≫ g = (L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ)) (img hg P) (img hg Q)).1)
    {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' f') (n : ℕ) :
    letI := L.pointGroup (t' ≫ Spec.map (CommRingCat.ofHom φ)); letI := L'.pointGroup t'
    img hg (P ^ n) = (img hg P) ^ n := by
  letI := L.pointGroup (t' ≫ Spec.map (CommRingCat.ofHom φ)); letI := L'.pointGroup t'
  let F : SchemeHomOver t' f' →* SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom φ)) f :=
    { toFun := img hg, map_one' := img_one hg L L' hg_mul t', map_mul' := fun X Y => img_mul hg L L' hg_mul t' X Y }
  exact map_pow F P n

end Square

section OneBase

variable {S : Type} [CommRing S] {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

theorem mapPt_one {E E' : FakeEllipticCurve Λ N S} (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f)
    (hmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) : mapPt φ hφ (E.L.one t) = E'.L.one t := by
  set x := mapPt φ hφ (E.L.one t) with hx
  have hxx : E'.L.mul t x x = x := by rw [hx, ← hmul, E.L.one_mul]
  letI := E'.L.pointGroup t
  have h2 : x * x = x * 1 := by rw [mul_one]; exact hxx
  exact mul_left_cancel h2

theorem mapPt_pow {E E' : FakeEllipticCurve Λ N S} (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f)
    (hmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f) (n : ℕ) :
    letI := E.L.pointGroup t; letI := E'.L.pointGroup t
    mapPt φ hφ (P ^ n) = (mapPt φ hφ P) ^ n := by
  letI := E.L.pointGroup t; letI := E'.L.pointGroup t
  let F : SchemeHomOver t E.f →* SchemeHomOver t E'.f :=
    { toFun := mapPt φ hφ, map_one' := mapPt_one φ hφ hmul t, map_mul' := fun X Y => hmul t X Y }
  exact map_pow F P n

theorem nsmulPt_eq_pow {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ) (P : SchemeHomOver t f) :
    letI := L.pointGroup t; nsmulPt L t n P = P ^ n := by
  letI := L.pointGroup t
  induction n with
  | zero => rw [pow_zero]; rfl
  | succ n ih => rw [pow_succ, ← ih]; rfl

end OneBase

section Natural
variable {S : Type} [CommRing S]

theorem act_congr {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (E : FakeEllipticCurve Λ N S) {x y : ℍ[ℚ, a, b]}
    (h : x = y) (hx : x ∈ Λ) (hy : y ∈ Λ) : E.act ⟨x, hx⟩ = E.act ⟨y, hy⟩ := by
  subst h; rfl

theorem pow_natural {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    {T T' : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (t' : T' ⟶ Spec (CommRingCat.of S)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (P : SchemeHomOver t f) (k : ℕ) :
    letI := L.pointGroup t; letI := L.pointGroup t'
    schemeHomOverComp ψ hψ (P ^ k) = (schemeHomOverComp ψ hψ P) ^ k := by
  letI := L.pointGroup t; letI := L.pointGroup t'
  let F : SchemeHomOver t f →* SchemeHomOver t' f :=
    { toFun := schemeHomOverComp ψ hψ, map_one' := L.one_natural t t' ψ hψ, map_mul' := fun X Y => L.mul_natural t t' ψ hψ X Y }
  exact map_pow F P k

theorem eq_of_pow_eq_pow_of_coprime {G : Type} [Group G] {a b : G} {M n : ℕ} (hcop : Nat.Coprime M n)
    (ha : a ^ n = 1) (hb : b ^ n = 1) (h : a ^ M = b ^ M) : a = b := by
  rcases Nat.lt_or_ge 1 n with hn | hn
  · obtain ⟨s, -, hs⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hn
    have key : ∀ c : G, c ^ n = 1 → (c ^ M) ^ s = c := by
      intro c hc
      have := Nat.div_add_mod (M * s) n
      rw [hs, mul_comm] at this
      rw [← pow_mul, ← this, pow_add, pow_one, pow_mul', hc, one_pow, one_mul]
    rw [← key a ha, ← key b hb, h]
  · interval_cases n
    ·
      have hM : M = 1 := by simpa [Nat.coprime_zero_right] using hcop
      simpa [hM] using h
    · simpa using ha.trans hb.symm

end Natural

end TRNpAsm
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_fullLevel_eq_of_isNormLevelTransport_of_isNormLevelTransport_frobTwist_one_of_isActBy.TRNpAsm"

open TRNpAsm in
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
    (hprA : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π (Fr : Onr →ₐ[𝒪] Onr)) A₀ A₀r prA)
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
    (F_frob : ∀ (C : Type) [CommRing C] [CharP C r] (x : Spec (CommRingCat.of C) ⟶ A₀.A),
      x ≫ F ≫ prA = Spec.map (CommRingCat.ofHom (frobenius C r)) ≫ x)

    (B : Type) [CommRing B] [IsNoetherianRing B] [Nontrivial B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (hBπ : IsNilpotent (algebraMap 𝒪 B π))
    (hconn : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1)
    (E : FakeEllipticCurve Λ N B) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E)
    (ρp : FakeEllipticCurve.Rigidification r π A₀ (frobTwist Onr Fr (1) ψ) E)
    (ub : ρ.Eb.A ⟶ ρp.Eb.A) (hub : ub ≫ ρp.gb = ρ.gb) (hub' : ub ≫ ρp.Eb.f = ρ.Eb.f)
    (gA' : ρp.Ab.A ⟶ A₀r.A) (hgA' : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π ψ) A₀r ρp.Ab gA')
    (hgA'' : gA' ≫ prA = ρp.gA)
    (Fb : ρ.Ab.A ⟶ ρp.Ab.A) (hFb : Fb ≫ gA' = ρ.gA ≫ F) (hFb' : Fb ≫ ρp.Ab.f = ρ.Ab.f)
    (Vb : ρp.Ab.A ⟶ ρ.Ab.A) (hVb : Vb ≫ ρ.gA = gA' ≫ V) (hVb' : Vb ≫ ρ.Ab.f = ρp.Ab.f)
    (hd : ρp.d = ρ.d + 1) (hφ : ub ≫ ρp.φ = ρ.φ ≫ Fb) (hφ' : ρp.φ' = Vb ≫ ρ.φ' ≫ ub)

    (n : ℕ) (hn : IsUnit ((n : ℕ) : B)) (P₀ : A₀.FullLevel n) (Pn Pn' : E.FullLevel n)
    (h₁ : FakeEllipticCurve.Rigidification.IsNormLevelTransport Fr θ₀ κ β₀ Φ ι coord P₀ ρ Pn)
    (h₂ : FakeEllipticCurve.Rigidification.IsNormLevelTransport Fr θ₀ κ β₀ Φ ι coord P₀ ρp Pn')
    (c : ℤ)
    (hact : ModuliPackage.G.IsActBy ι Φ η Fr E₀ ((Units.map (algebraMap K₀ (Matrix (Fin 2) (Fin 2) K₀)).toMonoidHom
              (Units.mk0 (r : K₀) (Nat.cast_ne_zero.mpr (Fact.out : r.Prime).ne_zero))) ^ c)
        (Ξ B ψ hBπ ⟨E, ρ⟩) (Ξ B (frobTwist Onr Fr (1) ψ) hBπ ⟨E, ρp⟩)) :
    nsmulPt E.L (𝟙 _) (r ^ c.toNat) Pn'.P = nsmulPt E.L (𝟙 _) (r ^ (-c).toNat) Pn.P := by
  classical

  obtain ⟨Q, hQ, hQA, X₁, θ₁, hX₁, j₁, t₁, hj₁, ht₁, hrig₁, hadm₁, E1⟩ := h₁
  obtain ⟨Qp, hQp, hQpA, X₂, θ₂, hX₂, j₂, t₂, hj₂, ht₂, hrig₂, hadm₂, E2⟩ := h₂

  obtain ⟨-, c2⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.comp_eq_and_comp_eq_nsmulPt_of_frobTwist_one_sections
      (N := N) 𝒪 hdvr π hπ hcomplete hres hunr Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr Λ A₀ P₀.P
      A₀r prA hprA F hF V hV F_hom V_hom F_act V_act F_lev V_lev V_F F_V F_frob B ψ hBπ E ρ ρp ub hub hub' gA' hgA' hgA''
      Fb hFb hFb' Vb hVb hVb' Q hQ hQA Qp hQp hQpA
  have hn2 : (t₂.n : ℤ) = (t₁.n : ℤ) + 1 + c :=
    CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.n_eq_of_isRigTransport_of_isRigTransport_frobTwist_one_of_isActBy
      hrr hrN 𝒪 hdvr π hπ hcomplete hres hunr K₀ Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr hB Λ hΛ hΛℤ coord hcoord
      A₀ X₀ hX₀ θ₀ hA₀ ι Φ hΦ hΦ4 M hM η hη E₀ hE₀ κ hκ n₀ β₀ hβ₀ Ξ hΞleg hΞnat hΞiso hΞdef A₀r prA hprA F hF V hV F_hom V_hom
      F_act V_act F_lev V_lev V_F F_V F_frob B ψ hBπ hconn E ρ ρp ub hub hub' gA' hgA' hgA'' Fb hFb hFb' Vb hVb hVb'
      hd hφ hφ' X₁ θ₁ hX₁ j₁ t₁ hj₁ ht₁ hrig₁ hadm₁ X₂ θ₂ hX₂ j₂ t₂ hj₂ ht₂ hrig₂ hadm₂ c hact

  obtain ⟨hφo, hφ'o, -, φ'hom, -, -, -⟩ := ρ.isIsogenyPair
  obtain ⟨hgb, gbmul, -, -⟩ := ρ.isPullback_Eb

  let Smk := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})))
  have hR : Smk ≫ 𝟙 (Spec (CommRingCat.of B)) = 𝟙 _ ≫ Smk := by rw [Category.comp_id, Category.id_comp]
  let R : SchemeHomOver (𝟙 (Spec (CommRingCat.of B))) E.f → SchemeHomOver (𝟙 _ ≫ Smk) E.f :=
    fun σ => schemeHomOverComp Smk hR σ
  have hRcoe : ∀ σ : SchemeHomOver (𝟙 (Spec (CommRingCat.of B))) E.f, (R σ).1 = Smk ≫ σ.1 := fun σ => rfl
  letI GB := E.L.pointGroup (𝟙 (Spec (CommRingCat.of B)))
  letI G := E.L.pointGroup (𝟙 _ ≫ Smk)
  letI GA := ρ.Ab.L.pointGroup (𝟙 (Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π}))))
  letI GE := ρ.Eb.L.pointGroup (𝟙 (Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π}))))
  have Rpow : ∀ (σ : SchemeHomOver (𝟙 (Spec (CommRingCat.of B))) E.f) (k : ℕ), R (σ ^ k) = (R σ) ^ k :=
    fun σ k => pow_natural E.L _ _ Smk hR σ k
  have Rone : R 1 = 1 := E.L.one_natural _ _ Smk hR
  let Qh : SchemeHomOver (𝟙 (Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π})))) ρ.Ab.f := ⟨Q, hQ⟩
  let W : SchemeHomOver (𝟙 _ ≫ Smk) E.f := img hgb (mapPt ρ.φ' hφ'o Qh)

  have hW1 : (R Pn.P) ^ (r ^ t₁.n) = W := by
    rw [← Rpow, ← nsmulPt_eq_pow]
    apply Subtype.ext
    rw [hRcoe, E1]
    rfl

  have hW2 : (R Pn'.P) ^ (r ^ t₂.n) = W ^ r := by
    rw [← Rpow, ← nsmulPt_eq_pow]
    have hi : W ^ r = img hgb (mapPt ρ.φ' hφ'o (Qh ^ r)) := by
      rw [mapPt_pow ρ.φ' hφ'o φ'hom, img_pow hgb E.L ρ.Eb.L gbmul]
    rw [hi]
    apply Subtype.ext
    rw [hRcoe, E2, hφ', Category.assoc, Category.assoc, hub, ← Category.assoc Qp Vb, c2, nsmulPt_eq_pow]
    rfl

  have hrn : ¬ r ∣ n := by
    intro hdvd
    obtain ⟨k, hk⟩ := hdvd
    have hmem : ((r : ℕ) : 𝒪) ∈ Ideal.span {π} := hunr ▸ Ideal.subset_span rfl
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton.1 hmem
    obtain ⟨m, hm⟩ := hBπ
    have hrnil : IsNilpotent ((r : ℕ) : B) := by
      refine ⟨m, ?_⟩
      have : ((r : ℕ) : B) = algebraMap 𝒪 B π * algebraMap 𝒪 B u := by rw [← map_mul, ← hu, map_natCast]
      rw [this, mul_pow, hm, zero_mul]
    have hnnil : IsNilpotent ((n : ℕ) : B) := by
      rw [hk, Nat.cast_mul]; exact Commute.isNilpotent_mul_right (Commute.all _ _) hrnil
    obtain ⟨e, he⟩ := hnnil
    exact (hn.pow e).ne_zero he
  have hcop : Nat.Coprime (r ^ (t₁.n + 1)) n :=
    Nat.Coprime.pow_left _ (((Fact.out : r.Prime).coprime_iff_not_dvd).2 hrn)

  have torsR : ∀ (T : E.FullLevel n), (R T.P) ^ n = 1 := by
    intro T
    rw [← Rpow, ← nsmulPt_eq_pow, T.torsion]
    exact Rone

  have hexp : t₂.n + (-c).toNat = t₁.n + 1 + c.toNat := by
    have := Int.toNat_sub_toNat_neg c
    omega

  have hpow : ((R Pn'.P) ^ (r ^ c.toNat)) ^ (r ^ (t₁.n + 1)) = ((R Pn.P) ^ (r ^ (-c).toNat)) ^ (r ^ (t₁.n + 1)) := by
    rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add, add_comm (c.toNat), ← hexp, pow_add, pow_mul, hW2,
      ← hW1, ← pow_mul, ← pow_mul]
    congr 1
    ring

  have hcancel : (R Pn'.P) ^ (r ^ c.toNat) = (R Pn.P) ^ (r ^ (-c).toNat) := by
    apply eq_of_pow_eq_pow_of_coprime hcop _ _ hpow
    · rw [← pow_mul, mul_comm, pow_mul, torsR, one_pow]
    · rw [← pow_mul, mul_comm, pow_mul, torsR, one_pow]

  have hker : IsNilpotent (RingHom.ker (algebraMap B (B ⧸ Ideal.span {algebraMap 𝒪 B π}))) := by
    rw [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]
    obtain ⟨m, hm⟩ := hBπ
    exact ⟨m, by rw [Ideal.span_singleton_pow, hm, Ideal.span_singleton_eq_bot.2 rfl]; rfl⟩
  have hsurj : Function.Surjective (algebraMap B (B ⧸ Ideal.span {algebraMap 𝒪 B π})) := by
    rw [Ideal.Quotient.algebraMap_eq]; exact Ideal.Quotient.mk_surjective
  have tors : ∀ (T : E.FullLevel n) (k : ℕ),
      nsmulPt E.L (𝟙 _) n (nsmulPt E.L (𝟙 _) k T.P) = E.L.one (𝟙 _) := by
    intro T k
    rw [nsmulPt_eq_pow, nsmulPt_eq_pow, ← pow_mul, mul_comm, pow_mul, ← nsmulPt_eq_pow E.L _ n T.P, T.torsion, ← nsmulPt_eq_pow]
    clear hcancel hpow torsR hW1 hW2
    induction k with
    | zero => rfl
    | succ k ih =>
      show E.L.mul _ (nsmulPt E.L _ k (E.L.one _)) (E.L.one _) = E.L.one _
      rw [ih, E.L.one_mul]
  refine CerednikDrinfeld.QM.FakeEllipticCurve.eq_of_specMap_comp_eq_of_nsmulPt_eq_one_of_isNilpotent_ker n B
    (B ⧸ Ideal.span {algebraMap 𝒪 B π}) hsurj hker hn E _ _ (tors Pn' _) (tors Pn _) ?_
  rw [Ideal.Quotient.algebraMap_eq]
  rw [← Rpow, ← Rpow] at hcancel
  have := congrArg Subtype.val hcancel
  rw [hRcoe, hRcoe, ← nsmulPt_eq_pow, ← nsmulPt_eq_pow] at this
  exact this

end S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_fullLevel_eq_of_isNormLevelTransport_of_isNormLevelTransport_frobTwist_one_of_isActBy
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_fullLevel_eq_of_isNormLevelTransport_of_isNormLevelTransport_frobTwist_one_of_isActBy (solution)
