-- Prove2me | solution 1 for CerednikDrinfeld.QM.IsFineModuli.mem_of_ptF_comp_eq_of_rigid
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/c631c115-446b-51fd-898d-ca4bfb4325b6

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_P_eq_pushPt_act_and_isTwist
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_IsFineModuli_mem_of_ptF_comp_eq_of_rigid

set_option autoImplicit false

universe u

open scoped TensorProduct Quaternion NumberField
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

namespace GLUEaux

variable {R : Type u} [CommRing R]

theorem eq_one_of_mul_self {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (y : SchemeHomOver t f) (h : L.mul t y y = y) :
    y = L.one t := by
  have := congrArg (L.mul t (L.inv t y)) h
  rw [← L.mul_assoc, L.inv_mul_cancel, L.one_mul] at this
  exact this

theorem map_one_of_hom {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (L' : RelativeGroupLaw R f') (φ : A ⟶ A') (hφ : φ ≫ f' = f)
    (hhom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      mapPt φ hφ (L.mul t P Q) = L'.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    mapPt φ hφ (L.one t) = L'.one t := by
  apply eq_one_of_mul_self
  rw [← hhom, L.one_mul]

theorem map_nsmulPt_of_hom {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (L' : RelativeGroupLaw R f') (φ : A ⟶ A') (hφ : φ ≫ f' = f)
    (hhom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      mapPt φ hφ (L.mul t P Q) = L'.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (P : SchemeHomOver t f) :
    mapPt φ hφ (nsmulPt L t n P) = nsmulPt L' t n (mapPt φ hφ P) := by
  induction n with
  | zero => exact map_one_of_hom L L' φ hφ hhom t
  | succ n ih => simp only [nsmulPt]; rw [hhom, ih]

theorem mapPt_mapPt {A A' A'' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    {f'' : A'' ⟶ Spec (CommRingCat.of R)} (φ : A ⟶ A') (hφ : φ ≫ f' = f) (ψ : A' ⟶ A'') (hψ : ψ ≫ f'' = f')
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f) :
    mapPt ψ hψ (mapPt φ hφ P) = mapPt (φ ≫ ψ) (by rw [Category.assoc, hψ, hφ]) P := by
  apply Subtype.ext; simp [mapPt, Category.assoc]

theorem mapPt_congr {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    {φ φ' : A ⟶ A'} (h : φ = φ') (hφ : φ ≫ f' = f) (hφ' : φ' ≫ f' = f)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f) :
    mapPt φ hφ P = mapPt φ' hφ' P := by
  subst h; rfl

theorem mapPt_injective_of_isIso {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    (φ : A ⟶ A') (hφ : φ ≫ f' = f) [IsIso φ]
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {P Q : SchemeHomOver t f} (h : mapPt φ hφ P = mapPt φ hφ Q) :
    P = Q := by
  apply Subtype.ext
  have := congrArg Subtype.val h
  simp only [mapPt] at this
  exact (cancel_mono φ).1 this

end GLUEaux

namespace GLUEact

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type u} [CommRing S]

theorem natCast_mem (hΛ : IsOrder Λ) (n : ℕ) : ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
  have : ((n : ℚ) : ℍ[ℚ, a, b]) = (n : ℤ) • (1 : ℍ[ℚ, a, b]) := by
    rw [zsmul_eq_mul, mul_one]; norm_cast
  rw [this]; exact Λ.smul_mem _ hΛ.one_mem

theorem act_zero_apply (E : FakeEllipticCurve Λ N S) (h0 : (0 : ℍ[ℚ, a, b]) ∈ Λ)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f) :
    pushPt (E.act ⟨0, h0⟩) (E.act_over _) P = E.L.one t := by
  apply GLUEaux.eq_one_of_mul_self
  have := E.act_add ⟨0, h0⟩ ⟨0, h0⟩ t P
  have e : (⟨0, h0⟩ + ⟨0, h0⟩ : ↥Λ) = ⟨0, h0⟩ := by apply Subtype.ext; simp
  rw [e] at this
  exact this.symm

theorem act_natCast_apply (E : FakeEllipticCurve Λ N S) (hΛ : IsOrder Λ) (n : ℕ)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f) :
    pushPt (E.act ⟨((n : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ n⟩) (E.act_over _) P = nsmulPt E.L t n P := by
  induction n with
  | zero =>
    have e : (⟨((0 : ℕ) : ℚ), natCast_mem hΛ 0⟩ : ↥Λ) = ⟨0, by simpa using natCast_mem hΛ 0⟩ := by
      apply Subtype.ext; simp
    rw [show pushPt (E.act ⟨(((0 : ℕ) : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ 0⟩) (E.act_over _) P =
        pushPt (E.act ⟨0, by simpa using natCast_mem hΛ 0⟩) (E.act_over _) P from by
          simp only [pushPt]; exact GLUEaux.mapPt_congr (by rw [e]) _ _ P]
    exact act_zero_apply E _ t P
  | succ n ih =>
    have e : (⟨(((n + 1 : ℕ) : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ (n + 1)⟩ : ↥Λ) =
        ⟨((n : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ n⟩ + ⟨1, hΛ.one_mem⟩ := by
      apply Subtype.ext; push_cast; rfl
    rw [show pushPt (E.act ⟨(((n + 1 : ℕ) : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ (n + 1)⟩) (E.act_over _) P =
        pushPt (E.act (⟨((n : ℚ) : ℍ[ℚ, a, b]), natCast_mem hΛ n⟩ + ⟨1, hΛ.one_mem⟩)) (E.act_over _) P from by
          simp only [pushPt]; exact GLUEaux.mapPt_congr (by rw [e]) _ _ P]
    rw [E.act_add, ih]
    simp only [nsmulPt]
    congr 1
    simp only [pushPt]
    rw [GLUEaux.mapPt_congr (E.act_one hΛ.one_mem) _ (by simp) P]
    apply Subtype.ext; simp [mapPt]

end GLUEact

namespace GLUEgrp

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
  {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))

theorem inv_inv (x : SchemeHomOver t f) : L.inv t (L.inv t x) = x := by
  calc L.inv t (L.inv t x) = L.mul t (L.inv t (L.inv t x)) (L.one t) := (L.mul_one t _).symm
    _ = L.mul t (L.inv t (L.inv t x)) (L.mul t (L.inv t x) x) := by rw [L.inv_mul_cancel]
    _ = L.mul t (L.mul t (L.inv t (L.inv t x)) (L.inv t x)) x := by rw [L.mul_assoc]
    _ = x := by rw [L.inv_mul_cancel, L.one_mul]

theorem mul_inv_cancel (x : SchemeHomOver t f) : L.mul t x (L.inv t x) = L.one t := by
  have := L.inv_mul_cancel t (L.inv t x)
  rwa [inv_inv] at this

theorem eq_of_mul_inv_eq_one {x y : SchemeHomOver t f} (h : L.mul t x (L.inv t y) = L.one t) : x = y := by
  have := congrArg (fun z => L.mul t z y) h
  rw [L.mul_assoc, L.inv_mul_cancel, L.mul_one, L.one_mul] at this
  exact this

theorem nsmulPt_add (n m : ℕ) (P : SchemeHomOver t f) :
    nsmulPt L t (n + m) P = L.mul t (nsmulPt L t n P) (nsmulPt L t m P) := by
  induction m with
  | zero => simp [nsmulPt, L.mul_one]
  | succ m ih => rw [Nat.add_succ]; simp only [nsmulPt]; rw [ih, L.mul_assoc]

theorem nsmulPt_one_pt (n : ℕ) : nsmulPt L t n (L.one t) = L.one t := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [nsmulPt]; rw [ih, L.one_mul]

theorem nsmulPt_mul (n m : ℕ) (P : SchemeHomOver t f) :
    nsmulPt L t (n * m) P = nsmulPt L t n (nsmulPt L t m P) := by
  induction n with
  | zero => simp [nsmulPt]
  | succ n ih => rw [Nat.succ_mul, nsmulPt_add, ih]; simp only [nsmulPt]

theorem nsmulPt_mod_eq_one {n m : ℕ} (P : SchemeHomOver t f)
    (hn : nsmulPt L t n P = L.one t) (hm : nsmulPt L t m P = L.one t) : nsmulPt L t (n % m) P = L.one t := by
  have e : n = n / m * m + n % m := (Nat.div_add_mod' n m).symm
  have := hn
  rw [e, nsmulPt_add, nsmulPt_mul, hm, nsmulPt_one_pt, L.one_mul] at this
  exact this

theorem eq_one_of_nsmulPt_eq_one_of_coprime {r N : ℕ} (hc : Nat.Coprime r N) (P : SchemeHomOver t f)
    (hr : nsmulPt L t r P = L.one t) (hN : nsmulPt L t N P = L.one t) : P = L.one t := by
  have key : ∀ a b : ℕ, nsmulPt L t a P = L.one t → nsmulPt L t b P = L.one t → nsmulPt L t (Nat.gcd a b) P = L.one t := by
    intro a b
    refine Nat.gcd.induction a b (fun n _ hn => by simpa using hn) (fun m n _ ih hm hn => ?_)
    rw [Nat.gcd_rec]
    exact ih (nsmulPt_mod_eq_one L t P hn hm) hm
  have := key r N hr hN
  rw [hc] at this
  simpa [nsmulPt, L.one_mul] using this

end GLUEgrp

theorem solution
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (N m : ℕ)
    {𝒪 : Type} [CommRing 𝒪] (hm' : IsUnit ((m : ℕ) : 𝒪))

    {M : Scheme.{0}} {πM : M ⟶ Spec (CommRingCat.of 𝒪)}
    {ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM}
    (hM : IsFineModuli Λ N m M πM ptF)
    {G : Type} [Group G] [Finite G] {ρ : G →* Aut M} {χ : G → ↥Λ}
    (hρ : IsLevelTwistAction Λ N m M πM ptF G ρ χ)

    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓm : ℓ ∣ m)
    (L₀ : Submodule ℤ ℍ[ℚ, a, b]) (hL₀ : L₀ ≤ Λ) (hℓL₀ : ∀ x : ↥Λ, (ℓ : ℚ) • (x : ℍ[ℚ, a, b]) ∈ L₀)
    (hL₀_left : ∀ (y : ↥Λ) (x : ℍ[ℚ, a, b]), x ∈ L₀ → (y : ℍ[ℚ, a, b]) * x ∈ L₀)
    (hL₀_index : L₀.toAddSubgroup.relIndex Λ.toAddSubgroup = ℓ ^ 2)
    (H : Subgroup G) (hH : ∀ g : G, g ∈ H ↔ ∀ x : ℍ[ℚ, a, b], x ∈ L₀ → x * (χ g : ℍ[ℚ, a, b]) ∈ L₀)
    (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of 𝒪))
    (u : FakeEllipticCurve.WithFullLevel Λ N m k)
    (hrigid : ∀ (e : u.1.A ≅ u.1.A) (he : e.hom ≫ u.1.f = u.1.f),
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t u.1.f),
          mapPt e.hom he (u.1.L.mul t P Q) = u.1.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q)) →
      (∀ x : ↥Λ, u.1.act x ≫ e.hom = e.hom ≫ u.1.act x) →
      e.hom = 𝟙 u.1.A ∨
        ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t u.1.f),
          mapPt e.hom he P = u.1.L.inv t P)
    (g : G) (hg : (ptF k s u).1 ≫ (ρ g).hom = (ptF k s u).1) :
    g ∈ H := by
  classical
  have hO : IsOrder Λ := hΛ.1
  obtain ⟨E, P⟩ := u

  have unit_of : ∀ g₁ g₂ : G, g₁ * g₂ = 1 →
      ∃ y : ↥Λ, (χ g₁ : ℍ[ℚ, a, b]) * (χ g₂ : ℍ[ℚ, a, b]) - 1 = (m : ℚ) • (y : ℍ[ℚ, a, b]) := by
    intro g₁ g₂ h12
    obtain ⟨y₀, hy₀⟩ := hρ.label_one
    obtain ⟨y₁, hy₁⟩ := hρ.label_mul g₁ g₂
    rw [h12] at hy₁
    refine ⟨y₀ - y₁, ?_⟩
    have : (χ g₁ : ℍ[ℚ, a, b]) * (χ g₂ : ℍ[ℚ, a, b]) - 1 = ((χ 1 : ℍ[ℚ, a, b]) - 1) - ((χ 1 : ℍ[ℚ, a, b]) - χ g₁ * χ g₂) := by abel
    rw [this, hy₀, hy₁, Submodule.coe_sub, smul_sub]
  obtain ⟨P', hP'P, htw⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.exists_P_eq_pushPt_act_and_isTwist hO E P (χ g) (χ g⁻¹)
    (unit_of g g⁻¹ (mul_inv_cancel g)) (unit_of g⁻¹ g (inv_mul_cancel g))

  have hpt : ptF k s ⟨E, P⟩ = ptF k s ⟨E, P'⟩ := by
    apply Subtype.ext
    rw [hρ.twist g k s ⟨E, P⟩ ⟨E, P'⟩ htw]
    exact hg.symm
  obtain ⟨e, he, e_hom, e_act, e_lev, e_P⟩ := hM.ptF_injective k s ⟨E, P⟩ ⟨E, P'⟩ hpt

  have e_P' : mapPt e.hom he P.P = pushPt (E.act (χ g)) (E.act_over (χ g)) P.P := by rw [← hP'P]; exact e_P

  let f : ↥Λ → SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f := fun y => pushPt (E.act y) (E.act_over y) P.P
  have f_add : ∀ x y : ↥Λ, f (x + y) = E.L.mul _ (f x) (f y) := fun x y => E.act_add x y _ P.P
  have f_zero : f 0 = E.L.one _ := by
    show pushPt (E.act 0) (E.act_over 0) P.P = _
    exact GLUEact.act_zero_apply E Λ.zero_mem _ P.P
  have f_neg : ∀ x : ↥Λ, f (-x) = E.L.inv _ (f x) := by
    intro x
    apply GLUEgrp.eq_of_mul_inv_eq_one E.L
    rw [GLUEgrp.inv_inv, ← f_add, neg_add_cancel, f_zero]
  have f_one : f ⟨1, hO.one_mem⟩ = P.P := by
    show pushPt (E.act ⟨1, hO.one_mem⟩) _ P.P = P.P
    apply Subtype.ext; simp [pushPt, mapPt, E.act_one hO.one_mem]

  have key : ∃ ε : ↥Λ, ((ε : ℍ[ℚ, a, b]) = 1 ∨ (ε : ℍ[ℚ, a, b]) = -1) ∧ f (χ g - ε) = E.L.one _ := by
    rcases hrigid e he e_hom e_act with h1 | hinv
    · refine ⟨⟨1, hO.one_mem⟩, Or.inl rfl, ?_⟩
      rw [sub_eq_add_neg, f_add, f_neg, f_one]
      have : f (χ g) = P.P := by
        show pushPt (E.act (χ g)) (E.act_over (χ g)) P.P = P.P
        rw [← e_P']; apply Subtype.ext; simp [mapPt, h1]
      rw [this]; exact GLUEgrp.mul_inv_cancel E.L _ P.P
    · refine ⟨⟨-1, Λ.neg_mem hO.one_mem⟩, Or.inr (by simp), ?_⟩
      have : (χ g - ⟨-1, Λ.neg_mem hO.one_mem⟩ : ↥Λ) = χ g + ⟨1, hO.one_mem⟩ := by
        apply Subtype.ext; simp [sub_eq_add_neg]
      rw [this, f_add, f_one]
      have : f (χ g) = E.L.inv _ P.P := by
        show pushPt (E.act (χ g)) (E.act_over (χ g)) P.P = _
        rw [← e_P']; exact hinv _ P.P
      rw [this]; exact E.L.inv_mul_cancel _ P.P
  obtain ⟨ε, hε, hkill⟩ := key

  let bc₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f → SchemeHomOver (geomPoint k (RingHom.id k)) E.f :=
    fun S => schemeHomOverComp (geomPoint k (RingHom.id k)) (Category.comp_id _) S
  have bc₀_act : ∀ (x : ↥Λ) S, bc₀ (pushPt (E.act x) (E.act_over x) S) = pushPt (E.act x) (E.act_over x) (bc₀ S) := by
    intro x S; apply Subtype.ext; simp [bc₀, schemeHomOverComp, pushPt, mapPt, Category.assoc]
  have bc₀_one : bc₀ (E.L.one _) = E.L.one _ := E.L.one_natural _ _ (geomPoint k (RingHom.id k)) (Category.comp_id _)
  have hsec0 : FakeEllipticCurve.sectionAt P.P k (RingHom.id k) = bc₀ P.P := rfl
  have hann : pushPt (E.act (χ g - ε)) (E.act_over _) (FakeEllipticCurve.sectionAt P.P k (RingHom.id k)) = E.L.one _ := by
    rw [hsec0, ← bc₀_act]
    show bc₀ (f (χ g - ε)) = _
    rw [hkill, bc₀_one]
  obtain ⟨y, hy⟩ := (P.annihilator k (RingHom.id k) (χ g - ε)).1 hann

  rw [hH]
  intro x hx
  have hcg : (χ g : ℍ[ℚ, a, b]) = (ε : ℍ[ℚ, a, b]) + (m : ℚ) • (y : ℍ[ℚ, a, b]) := by
    rw [← hy, Submodule.coe_sub]; abel
  obtain ⟨m', hm'⟩ := hℓm
  have hxΛ : x ∈ Λ := hL₀ hx
  have hmxy : x * ((m : ℚ) • (y : ℍ[ℚ, a, b])) ∈ L₀ := by
    rw [mul_smul_comm, hm', Nat.cast_mul, mul_smul]
    have hmem : (m' : ℚ) • (x * (y : ℍ[ℚ, a, b])) ∈ Λ := by
      rw [← QuaternionAlgebra.coe_mul_eq_smul]
      exact hO.mul_mem (GLUEact.natCast_mem hO m') (hO.mul_mem hxΛ y.2)
    exact hℓL₀ ⟨_, hmem⟩
  rw [hcg, mul_add]
  refine L₀.add_mem ?_ hmxy
  rcases hε with h | h
  · rw [h, mul_one]; exact hx
  · rw [h, mul_neg_one]; exact L₀.neg_mem hx

end S_CerednikDrinfeld_QM_IsFineModuli_mem_of_ptF_comp_eq_of_rigid
end P2MW
export P2MW.S_CerednikDrinfeld_QM_IsFineModuli_mem_of_ptF_comp_eq_of_rigid (solution)
