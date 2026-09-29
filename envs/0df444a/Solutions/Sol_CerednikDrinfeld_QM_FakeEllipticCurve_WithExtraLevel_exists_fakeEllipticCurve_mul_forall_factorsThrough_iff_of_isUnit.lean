-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_fakeEllipticCurve_mul_forall_factorsThrough_iff_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/e3ba6ed5-5c83-54d3-af86-2f2188ba4e7c

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_exists_isClosedImmersion_factorsThrough_iff_nsmulPt
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_exists_zmod_mul_prod_equiv_factorsThrough_of_coprime
import Theorems.Thm_AlgebraicGeometry_isFinite_flat_and_finrank_pullback_fst_comp_eq_mul_of_finrank_eq_const
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_exists_fakeEllipticCurve_mul_forall_factorsThrough_iff_of_isUnit

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
p2m_open "CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_exists_fakeEllipticCurve_mul_forall_factorsThrough_iff_of_isUnit.CerednikDrinfeld CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_exists_fakeEllipticCurve_mul_forall_factorsThrough_iff_of_isUnit.CerednikDrinfeld.QM NeronModelInfra"

open CategoryTheory.Limits GoodReductionJacobian

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "QM.FakeEllipticCurve.WithExtraLevel QM.FakeEllipticCurve QM.FakeEllipticCurve.WithExtraLevel.exists_isClosedImmersion_factorsThrough_iff_nsmulPt QM.FakeEllipticCurve.WithExtraLevel.exists_zmod_mul_prod_equiv_factorsThrough_of_coprime"
namespace QM
p2m_export "CerednikDrinfeld.QM" "FakeEllipticCurve.WithExtraLevel mapPt pushPt FactorsThrough nsmulPt FakeEllipticCurve FakeEllipticCurve.WithExtraLevel.exists_isClosedImmersion_factorsThrough_iff_nsmulPt FakeEllipticCurve.WithExtraLevel.exists_zmod_mul_prod_equiv_factorsThrough_of_coprime"
namespace CombineExistsBody
p2m_open "CerednikDrinfeld.QM CerednikDrinfeld"

theorem zpow_mem_of_closed {G : Type*} [Group G] (M : G → Prop) (h1 : M 1)
    (hmul : ∀ x y, M x → M y → M (x * y)) (hinv : ∀ x, M x → M x⁻¹) {x : G} (hx : M x) (z : ℤ) : M (x ^ z) := by
  let H : Subgroup G := { carrier := {x | M x}, one_mem' := h1, mul_mem' := fun ha hb => hmul _ _ ha hb, inv_mem' := fun ha => hinv _ ha }
  exact H.zpow_mem (x := x) hx z

theorem bezout_int {N ℓ : ℕ} (h : N.Coprime ℓ) : ∃ α β : ℤ, (N : ℤ) * α + (ℓ : ℤ) * β = 1 := by
  refine ⟨N.gcdA ℓ, N.gcdB ℓ, ?_⟩
  have := Nat.gcd_eq_gcd_ab N ℓ
  rw [Nat.Coprime.gcd_eq_one h] at this
  exact_mod_cast this.symm

theorem eq_zpow_mul_zpow {G : Type*} [Group G] (x : G) {N ℓ : ℕ} {α β : ℤ} (h : (N : ℤ) * α + (ℓ : ℤ) * β = 1) :
    x = (x ^ N) ^ α * (x ^ ℓ) ^ β := by
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, h, zpow_one]

def subgroupOf {G : Type*} [Group G] (M : G → Prop) (h1 : M 1)
    (hmul : ∀ x y, M x → M y → M (x * y)) (hinv : ∀ x, M x → M x⁻¹) : Subgroup G :=
  { carrier := {x | M x}, one_mem' := h1, mul_mem' := fun ha hb => hmul _ _ ha hb, inv_mem' := fun ha => hinv _ ha }

theorem main
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N ℓ : ℕ) (hNℓ : N.Coprime ℓ)
    (S : Type) [CommRing S] (hu : IsUnit ((N * ℓ : ℕ) : S)) (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) :
    ∃ E' : FakeEllipticCurve Λ (N * ℓ) S, ∃ (e : u.1.A ≅ E'.A) (he : e.hom ≫ E'.f = u.1.f),
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t u.1.f),
          mapPt e.hom he (u.1.L.mul t P Q) = E'.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q)) ∧
        (∀ x : ↥Λ, u.1.act x ≫ e.hom = e.hom ≫ E'.act x) ∧
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
          FactorsThrough u.1.lev P ↔
            FactorsThrough E'.lev (mapPt e.hom he P) ∧ nsmulPt E'.L t N (mapPt e.hom he P) = E'.L.one t) ∧
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
          FactorsThrough u.2.levK P ↔
            FactorsThrough E'.lev (mapPt e.hom he P) ∧ nsmulPt E'.L t ℓ (mapPt e.hom he P) = E'.L.one t) := by
  classical
  obtain ⟨α, β, hαβ⟩ := bezout_int hNℓ
  set E := u.1 with hE
  set K := u.2 with hK
  have hcomm : E.L.IsCommutative := E.comm

  obtain ⟨C', lev', hcl, hchar⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_isClosedImmersion_factorsThrough_iff_nsmulPt Λ N ℓ S u

  have PT : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)),
      (∀ P Q : SchemeHomOver t E.f, FactorsThrough lev' P → FactorsThrough lev' Q →
          FactorsThrough lev' (E.L.mul t P Q) ∧ FactorsThrough lev' (E.L.inv t P)) ∧
      FactorsThrough lev' (E.L.one t) ∧
      (∀ P : SchemeHomOver t E.f, FactorsThrough lev' P → nsmulPt E.L t (N * ℓ) P = E.L.one t) ∧
      (∀ (x : ↥Λ) (P : SchemeHomOver t E.f), FactorsThrough lev' P → FactorsThrough lev' (pushPt (E.act x) (E.act_over x) P)) ∧
      (∀ P : SchemeHomOver t E.f, FactorsThrough E.lev P ↔ FactorsThrough lev' P ∧ nsmulPt E.L t N P = E.L.one t) ∧
      (∀ P : SchemeHomOver t E.f, FactorsThrough K.levK P ↔ FactorsThrough lev' P ∧ nsmulPt E.L t ℓ P = E.L.one t) ∧
      (∀ P : SchemeHomOver t E.f, FactorsThrough lev' P →
          ∃ c κ : SchemeHomOver t E.f, FactorsThrough E.lev c ∧ FactorsThrough K.levK κ ∧ E.L.mul t c κ = P) ∧
      (∀ c κ c' κ' : SchemeHomOver t E.f, FactorsThrough E.lev c → FactorsThrough K.levK κ →
          FactorsThrough E.lev c' → FactorsThrough K.levK κ' → E.L.mul t c κ = E.L.mul t c' κ' → c = c' ∧ κ = κ') := by
    intro T t
    letI : CommGroup (SchemeHomOver t E.f) := { E.L.pointGroup t with mul_comm := fun x y => hcomm t x y }
    have hmul : ∀ x y : SchemeHomOver t E.f, E.L.mul t x y = x * y := fun _ _ => rfl
    have hone : E.L.one t = 1 := rfl
    have hinv : ∀ x : SchemeHomOver t E.f, E.L.inv t x = x⁻¹ := fun _ => rfl
    have hcm : ∀ x y : SchemeHomOver t E.f, x * y = y * x := fun x y => hcomm t x y
    have hpow : ∀ (n : ℕ) (P : SchemeHomOver t E.f), nsmulPt E.L t n P = P ^ n := by
      intro n P
      induction n with
      | zero => exact (pow_zero P).symm
      | succ n ih =>
        rw [show nsmulPt E.L t (n + 1) P = E.L.mul t (nsmulPt E.L t n P) P from rfl, ih, pow_succ]; rfl

    let HC : Subgroup (SchemeHomOver t E.f) := subgroupOf (fun P => FactorsThrough E.lev P) (E.lev_one t)
      (fun x y hx hy => (E.lev_sub t x y hx hy).1) (fun x hx => (E.lev_sub t x x hx hx).2)
    let HK : Subgroup (SchemeHomOver t E.f) := subgroupOf (fun P => FactorsThrough K.levK P) (K.levK_one t)
      (fun x y hx hy => (K.levK_sub t x y hx hy).1) (fun x hx => (K.levK_sub t x x hx hx).2)
    have hchar' : ∀ P : SchemeHomOver t E.f, FactorsThrough lev' P ↔ P ^ ℓ ∈ HC ∧ P ^ N ∈ HK := by
      intro P; rw [hchar, hpow, hpow]; exact Iff.rfl
    have torsC : ∀ P, P ∈ HC → P ^ N = 1 := fun P hP => by rw [← hpow, ← hone]; exact E.lev_torsion t P hP
    have torsK : ∀ P, P ∈ HK → P ^ ℓ = 1 := fun P hP => by rw [← hpow, ← hone]; exact K.levK_torsion t P hP

    have one' : FactorsThrough lev' (E.L.one t) := by
      rw [hone, hchar', one_pow, one_pow]; exact ⟨HC.one_mem, HK.one_mem⟩
    have sub' : ∀ P Q : SchemeHomOver t E.f, FactorsThrough lev' P → FactorsThrough lev' Q →
        FactorsThrough lev' (E.L.mul t P Q) ∧ FactorsThrough lev' (E.L.inv t P) := by
      intro P Q hP hQ
      rw [hchar'] at hP hQ
      rw [hmul, hinv, hchar', hchar', mul_pow, mul_pow, inv_pow, inv_pow]
      exact ⟨⟨HC.mul_mem hP.1 hQ.1, HK.mul_mem hP.2 hQ.2⟩, HC.inv_mem hP.1, HK.inv_mem hP.2⟩

    have hCC' : ∀ P, P ∈ HC → FactorsThrough lev' P := fun P hP => by
      rw [hchar']; exact ⟨HC.pow_mem hP ℓ, by rw [torsC P hP]; exact HK.one_mem⟩
    have hKC' : ∀ P, P ∈ HK → FactorsThrough lev' P := fun P hP => by
      rw [hchar']; exact ⟨by rw [torsK P hP]; exact HC.one_mem, HK.pow_mem hP N⟩

    have decomp : ∀ P : SchemeHomOver t E.f, P = (P ^ N) ^ α * (P ^ ℓ) ^ β := fun P => eq_zpow_mul_zpow P hαβ

    have disj : ∀ P, P ∈ HC → P ∈ HK → P = 1 := fun P hC hKK => by
      rw [← hone]; exact K.levK_disjoint t P hKK hC
    refine ⟨sub', one', ?tors, ?stab, ?charC, ?charK, ?dec, ?uniq⟩
    case tors =>
      intro P hP
      rw [hchar'] at hP
      rw [hpow, hone, mul_comm N ℓ, pow_mul]
      exact torsC _ hP.1
    case stab =>
      intro x P hP
      rw [hchar'] at hP ⊢
      let ax : SchemeHomOver t E.f →* SchemeHomOver t E.f :=
        MonoidHom.mk' (fun Q => pushPt (E.act x) (E.act_over x) Q) (fun P Q => E.act_hom x t P Q)
      have hax : ∀ Q, pushPt (E.act x) (E.act_over x) Q = ax Q := fun _ => rfl
      rw [hax, ← map_pow, ← map_pow]
      exact ⟨E.lev_stable x t _ hP.1, K.levK_stable x t _ hP.2⟩
    case charC =>
      intro P
      constructor
      · intro hP
        exact ⟨hCC' P hP, by rw [hpow, hone]; exact torsC P hP⟩
      · rintro ⟨hP, hN⟩
        rw [hchar'] at hP
        rw [hpow, hone] at hN
        show P ∈ HC
        rw [decomp P, hN, one_zpow, one_mul]
        exact HC.zpow_mem hP.1 β
    case charK =>
      intro P
      constructor
      · intro hP
        exact ⟨hKC' P hP, by rw [hpow, hone]; exact torsK P hP⟩
      · rintro ⟨hP, hl⟩
        rw [hchar'] at hP
        rw [hpow, hone] at hl
        show P ∈ HK
        rw [decomp P, hl, one_zpow, mul_one]
        exact HK.zpow_mem hP.2 α
    case dec =>
      intro P hP
      rw [hchar'] at hP
      refine ⟨(P ^ ℓ) ^ β, (P ^ N) ^ α, HC.zpow_mem hP.1 β, HK.zpow_mem hP.2 α, ?_⟩
      rw [hmul, hcm, ← decomp P]
    case uniq =>
      intro c κ c' κ' hc hκ hc' hκ' h
      rw [hmul, hmul] at h

      have hd : c⁻¹ * c' = κ * κ'⁻¹ := by
        have h2 : c' * κ' = c * κ := h.symm
        calc c⁻¹ * c' = c⁻¹ * c' * (κ' * κ'⁻¹) := by rw [mul_inv_cancel, mul_one]
          _ = c⁻¹ * (c' * κ') * κ'⁻¹ := by simp only [mul_assoc]
          _ = c⁻¹ * (c * κ) * κ'⁻¹ := by rw [h2]
          _ = κ * κ'⁻¹ := by rw [← mul_assoc, inv_mul_cancel, one_mul]
      have hdC : c⁻¹ * c' ∈ HC := HC.mul_mem (HC.inv_mem hc) hc'
      have hdK : c⁻¹ * c' ∈ HK := by rw [hd]; exact HK.mul_mem hκ (HK.inv_mem hκ')
      have hd1 : c⁻¹ * c' = 1 := disj _ hdC hdK
      have hcc : c = c' := by
        rw [inv_mul_eq_one] at hd1; exact hd1
      refine ⟨hcc, ?_⟩
      rw [hcc] at h
      exact mul_left_cancel h

  haveI : IsClosedImmersion E.lev := E.lev_closed
  haveI : IsClosedImmersion K.levK := K.levK_closed
  haveI : IsClosedImmersion lev' := hcl
  haveI : IsFinite (E.lev ≫ E.f) := E.lev_finite
  haveI : Flat (E.lev ≫ E.f) := E.lev_flat
  haveI : LocallyOfFinitePresentation (E.lev ≫ E.f) := E.lev_finitePresentation
  haveI : IsFinite (K.levK ≫ E.f) := K.levK_finite
  haveI : Flat (K.levK ≫ E.f) := K.levK_flat
  haveI : LocallyOfFinitePresentation (K.levK ≫ E.f) := K.levK_finitePresentation
  obtain ⟨hXfin, hXflat, hXlfp, hXrank⟩ :=
    AlgebraicGeometry.isFinite_flat_and_finrank_pullback_fst_comp_eq_mul_of_finrank_eq_const (E.lev ≫ E.f) (K.levK ≫ E.f)
      (N ^ 2) (ℓ ^ 2) E.lev_rank K.levK_rank

  set tX : pullback (E.lev ≫ E.f) (K.levK ≫ E.f) ⟶ Spec (CommRingCat.of S) :=
    pullback.fst (E.lev ≫ E.f) (K.levK ≫ E.f) ≫ (E.lev ≫ E.f) with htX
  let PX : SchemeHomOver tX E.f := ⟨pullback.fst (E.lev ≫ E.f) (K.levK ≫ E.f) ≫ E.lev, by rw [htX, Category.assoc]⟩
  let QX : SchemeHomOver tX E.f := ⟨pullback.snd (E.lev ≫ E.f) (K.levK ≫ E.f) ≫ K.levK, by
    rw [htX, Category.assoc, pullback.condition]⟩
  have hPX : FactorsThrough E.lev PX := ⟨pullback.fst _ _, rfl⟩
  have hQX : FactorsThrough K.levK QX := ⟨pullback.snd _ _, rfl⟩
  obtain ⟨hsubX, -, -, -, hcharCX, hcharKX, -, huniqX⟩ := PT tX
  have hSum : FactorsThrough lev' (E.L.mul tX PX QX) :=
    (hsubX PX QX ((hcharCX PX).1 hPX).1 ((hcharKX QX).1 hQX).1).1
  obtain ⟨σ, hσ⟩ := hSum

  set tC : C' ⟶ Spec (CommRingCat.of S) := lev' ≫ E.f with htC
  let Pi : SchemeHomOver tC E.f := ⟨lev', rfl⟩
  have hPi : FactorsThrough lev' Pi := ⟨𝟙 _, Category.id_comp _⟩
  obtain ⟨hsubC, -, -, -, -, -, hdecC, -⟩ := PT tC
  obtain ⟨c, κ, hc, hκ, hcκ⟩ := hdecC Pi hPi
  obtain ⟨c₀, hc₀⟩ := hc
  obtain ⟨κ₀, hκ₀⟩ := hκ
  have hcf : c₀ ≫ (E.lev ≫ E.f) = tC := by rw [← Category.assoc, hc₀]; exact c.2
  have hκf : κ₀ ≫ (K.levK ≫ E.f) = tC := by rw [← Category.assoc, hκ₀]; exact κ.2
  let τ : C' ⟶ pullback (E.lev ≫ E.f) (K.levK ≫ E.f) := pullback.lift c₀ κ₀ (by rw [hcf, hκf])
  have hτfst : τ ≫ pullback.fst _ _ = c₀ := pullback.lift_fst _ _ _
  have hτsnd : τ ≫ pullback.snd _ _ = κ₀ := pullback.lift_snd _ _ _
  have hτfst' : ∀ {Z : Scheme.{0}} (m : E.C ⟶ Z), τ ≫ pullback.fst _ _ ≫ m = c₀ ≫ m := fun m => by
    rw [← Category.assoc, hτfst]
  have hτsnd' : ∀ {Z : Scheme.{0}} (m : K.K ⟶ Z), τ ≫ pullback.snd _ _ ≫ m = κ₀ ≫ m := fun m => by
    rw [← Category.assoc, hτsnd]
  have hτ : τ ≫ tX = tC := by rw [htX, ← Category.assoc, hτfst, hcf]
  have hσ' : σ ≫ tC = tX := by
    rw [htC, ← Category.assoc, hσ]; exact (E.L.mul tX PX QX).2

  have h1 : τ ≫ σ = 𝟙 C' := by
    rw [← cancel_mono lev', Category.assoc, hσ, Category.id_comp]
    have hnat := congrArg Subtype.val (E.L.mul_natural tX tC τ hτ PX QX)
    rw [schemeHomOverComp_coe] at hnat
    have eP : schemeHomOverComp τ hτ PX = c := Subtype.ext (by
      rw [schemeHomOverComp_coe, ← hc₀, ← hτfst, Category.assoc])
    have eQ : schemeHomOverComp τ hτ QX = κ := Subtype.ext (by
      rw [schemeHomOverComp_coe, ← hκ₀, ← hτsnd, Category.assoc])
    rw [eP, eQ, hcκ] at hnat
    exact hnat

  have hσc : schemeHomOverComp σ hσ' c = PX ∧ schemeHomOverComp σ hσ' κ = QX := by
    apply huniqX
    · exact ⟨σ ≫ c₀, by rw [schemeHomOverComp_coe, Category.assoc, hc₀]⟩
    · exact ⟨σ ≫ κ₀, by rw [schemeHomOverComp_coe, Category.assoc, hκ₀]⟩
    · exact hPX
    · exact hQX
    · rw [← E.L.mul_natural tC tX σ hσ' c κ, hcκ]
      exact Subtype.ext (by rw [schemeHomOverComp_coe]; exact hσ)
  have h2 : σ ≫ τ = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.id_comp, ← cancel_mono E.lev, Category.assoc, Category.assoc, hτfst', hc₀]
      have := congrArg Subtype.val hσc.1
      rwa [schemeHomOverComp_coe] at this
    · rw [Category.id_comp, ← cancel_mono K.levK, Category.assoc, Category.assoc, hτsnd', hκ₀]
      have := congrArg Subtype.val hσc.2
      rwa [schemeHomOverComp_coe] at this
  let eX : pullback (E.lev ≫ E.f) (K.levK ≫ E.f) ≅ C' := ⟨σ, τ, h2, h1⟩
  haveI : IsIso τ := eX.isIso_inv
  have hlevf : lev' ≫ E.f = τ ≫ (pullback.fst (E.lev ≫ E.f) (K.levK ≫ E.f) ≫ (E.lev ≫ E.f)) := by
    rw [← htX, hτ]
  haveI := hXfin; haveI := hXflat; haveI := hXlfp
  have lev_finite' : IsFinite (lev' ≫ E.f) := by rw [hlevf]; infer_instance
  have lev_flat' : Flat (lev' ≫ E.f) := by rw [hlevf]; infer_instance
  have lev_fp' : LocallyOfFinitePresentation (lev' ≫ E.f) := by rw [hlevf]; infer_instance
  have lev_rank' : ∀ s : ↥(Spec (CommRingCat.of S)), (lev' ≫ E.f).finrank s = (N * ℓ) ^ 2 := by
    intro s
    rw [hlevf, Scheme.Hom.finrank_comp_left_of_isIso, hXrank, mul_pow]

  let E' : FakeEllipticCurve Λ (N * ℓ) S :=
    { A := E.A, f := E.f, L := E.L, comm := E.comm, bundle := E.bundle, dim_fibre := E.dim_fibre,
      act := E.act, act_over := E.act_over, act_hom := E.act_hom, act_one := E.act_one, act_mul := E.act_mul,
      act_add := E.act_add, act_trace := E.act_trace,
      C := C', lev := lev', lev_closed := hcl,
      lev_sub := fun t P Q hP hQ => (PT t).1 P Q hP hQ,
      lev_one := fun t => (PT t).2.1,
      lev_torsion := fun t P hP => (PT t).2.2.1 P hP,
      lev_stable := fun x T t P hP => (PT t).2.2.2.1 x P hP,
      lev_finite := lev_finite', lev_flat := lev_flat', lev_finitePresentation := lev_fp', lev_rank := lev_rank',
      lev_fibre := fun k _ _ sk hk =>
        CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_zmod_mul_prod_equiv_factorsThrough_of_coprime Λ N ℓ hNℓ S u
          lev' hchar k sk hk }
  have mapPt_id : ∀ {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t E.f)
      (h : (Iso.refl E.A).hom ≫ E.f = E.f), mapPt (Iso.refl E.A).hom h P = P :=
    fun P h => Subtype.ext (Category.comp_id _)
  refine ⟨E', Iso.refl E.A, Category.id_comp _, ?_, ?_, ?_, ?_⟩
  · intro T t P Q
    rw [mapPt_id, mapPt_id, mapPt_id]
  · intro x
    show E.act x ≫ 𝟙 E.A = 𝟙 E.A ≫ E.act x
    rw [Category.comp_id, Category.id_comp]
  · intro T t P
    rw [mapPt_id]
    exact (PT t).2.2.2.2.1 P
  · intro T t P
    rw [mapPt_id]
    exact (PT t).2.2.2.2.2.1 P

end CerednikDrinfeld.QM.CombineExistsBody

theorem solution
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N ℓ : ℕ) (hNℓ : N.Coprime ℓ)
    (S : Type) [CommRing S] (hu : IsUnit ((N * ℓ : ℕ) : S)) (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) :
    ∃ E' : FakeEllipticCurve Λ (N * ℓ) S, ∃ (e : u.1.A ≅ E'.A) (he : e.hom ≫ E'.f = u.1.f),
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t u.1.f),
          mapPt e.hom he (u.1.L.mul t P Q) = E'.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q)) ∧
        (∀ x : ↥Λ, u.1.act x ≫ e.hom = e.hom ≫ E'.act x) ∧
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
          FactorsThrough u.1.lev P ↔
            FactorsThrough E'.lev (mapPt e.hom he P) ∧ nsmulPt E'.L t N (mapPt e.hom he P) = E'.L.one t) ∧
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
          FactorsThrough u.2.levK P ↔
            FactorsThrough E'.lev (mapPt e.hom he P) ∧ nsmulPt E'.L t ℓ (mapPt e.hom he P) = E'.L.one t) :=
  CerednikDrinfeld.QM.CombineExistsBody.main Λ N ℓ hNℓ S hu u

end S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_exists_fakeEllipticCurve_mul_forall_factorsThrough_iff_of_isUnit
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_exists_fakeEllipticCurve_mul_forall_factorsThrough_iff_of_isUnit (solution)
