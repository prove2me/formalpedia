-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_monoidHom_units_zmod_eq_pow_of_endomorphismDictionary_slack_of_comm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/20bffe5f-7734-507c-84a5-fbd3f237fa1a

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_apply_nilEval_natCast_eq_mapPt_act_of_isFormalModuleVia
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_IsFormalCoordinates_eq_of_forall_apply_nilEval_eq
import Theorems.Thm_MvFormalGroup_nilEval_subst_of_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_monoidHom_units_zmod_eq_pow_of_endomorphismDictionary_slack_of_comm

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

namespace KCHARdd

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}

def Cong (Λ : Submodule ℤ ℍ[ℚ, a, b]) (n : ℕ) (x y : ℍ[ℚ, a, b]) : Prop :=
  ∃ z : ↥Λ, x - y = (n : ℚ) • (z : ℍ[ℚ, a, b])

theorem Cong.refl (n : ℕ) (x : ℍ[ℚ, a, b]) : Cong Λ n x x := ⟨0, by simp⟩

theorem Cong.symm {n : ℕ} {x y : ℍ[ℚ, a, b]} (h : Cong Λ n x y) : Cong Λ n y x := by
  obtain ⟨z, hz⟩ := h
  refine ⟨-z, ?_⟩
  rw [Submodule.coe_neg, smul_neg, ← hz, neg_sub]

theorem Cong.trans {n : ℕ} {x y w : ℍ[ℚ, a, b]} (h : Cong Λ n x y) (h' : Cong Λ n y w) : Cong Λ n x w := by
  obtain ⟨z, hz⟩ := h
  obtain ⟨z', hz'⟩ := h'
  refine ⟨z + z', ?_⟩
  rw [Submodule.coe_add, smul_add, ← hz, ← hz', sub_add_sub_cancel]

theorem Cong.mul (hΛ : IsOrder Λ) {n : ℕ} {x x' y y' : ℍ[ℚ, a, b]} (hx : Cong Λ n x x') (hy : Cong Λ n y y')
    (hy0 : y ∈ Λ) (hx'0 : x' ∈ Λ) : Cong Λ n (x * y) (x' * y') := by
  obtain ⟨z, hz⟩ := hx
  obtain ⟨w, hw⟩ := hy
  refine ⟨⟨(z : ℍ[ℚ, a, b]) * y + x' * (w : ℍ[ℚ, a, b]), Λ.add_mem (hΛ.mul_mem z.2 hy0) (hΛ.mul_mem hx'0 w.2)⟩, ?_⟩
  have : x * y - x' * y' = (x - x') * y + x' * (y - y') := by
    rw [sub_mul, mul_sub]; abel
  rw [this, hz, hw, smul_mul_assoc, mul_smul_comm, ← smul_add]

theorem exists_int_of_coe_mem (hΛ : IsOrder Λ) (q : ℚ) (hq : ((q : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) : ∃ m : ℤ, (m : ℚ) = q := by
  let S : Subalgebra ℤ ℍ[ℚ, a, b] :=
    { carrier := Λ
      mul_mem' := fun hx hy => hΛ.mul_mem hx hy
      one_mem' := hΛ.one_mem
      add_mem' := fun hx hy => Λ.add_mem hx hy
      zero_mem' := Λ.zero_mem
      algebraMap_mem' := fun m => by
        rw [Algebra.algebraMap_eq_smul_one]
        exact Λ.smul_mem m hΛ.one_mem }
  have hS : S.toSubmodule = Λ := rfl
  have hint : IsIntegral ℤ ((q : ℚ) : ℍ[ℚ, a, b]) := IsIntegral.of_mem_of_fg S (hS ▸ hΛ.fg) _ hq
  have hint' : IsIntegral ℤ q := by
    have hinj : Function.Injective (IsScalarTower.toAlgHom ℤ ℚ ℍ[ℚ, a, b]) := (algebraMap ℚ ℍ[ℚ, a, b]).injective
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ ℚ ℍ[ℚ, a, b]) hinj).mp hint
  obtain ⟨m, hm⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).mp hint'
  exact ⟨m, by simpa using hm⟩

theorem zmod_eq_of_cong (hΛ : IsOrder Λ) {n : ℕ} [NeZero n] (c d : ℤ)
    (h : Cong Λ n (((c : ℚ)) : ℍ[ℚ, a, b]) (((d : ℚ)) : ℍ[ℚ, a, b])) : (c : ZMod n) = (d : ZMod n) := by
  obtain ⟨z, hz⟩ := h
  have hn : (n : ℚ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  have hz' : (z : ℍ[ℚ, a, b]) = ((((n : ℚ))⁻¹ * ((c : ℚ) - (d : ℚ)) : ℚ) : ℍ[ℚ, a, b]) := by
    have : ((n : ℚ)⁻¹ : ℚ) • ((n : ℚ) • (z : ℍ[ℚ, a, b])) = (z : ℍ[ℚ, a, b]) := by
      rw [smul_smul, inv_mul_cancel₀ hn, one_smul]
    rw [← this, ← hz, ← QuaternionAlgebra.coe_sub, QuaternionAlgebra.smul_coe]
  obtain ⟨m, hm⟩ := exists_int_of_coe_mem hΛ _ (hz' ▸ z.2)
  have hcd : (c : ℚ) - (d : ℚ) = (n : ℚ) * (m : ℚ) := by
    rw [hm, ← mul_assoc, mul_inv_cancel₀ hn, one_mul]
  have hcd' : c - d = (n : ℤ) * m := by exact_mod_cast hcd
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
  exact ⟨-m, by linarith⟩

section Act

variable {N : ℕ} {S : Type} [CommRing S] (A : FakeEllipticCurve Λ N S)

theorem pushPt_act_congr {x y : ↥Λ} (h : x = y) {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)}
    (P : SchemeHomOver t A.f) : pushPt (A.act x) (A.act_over x) P = pushPt (A.act y) (A.act_over y) P := by
  subst h; rfl

theorem cong_of_pushPt_act_eq [Nontrivial S] {n : ℕ} (P : A.FullLevel n) (x y : ↥Λ)
    (h : pushPt (A.act x) (A.act_over x) P.P = pushPt (A.act y) (A.act_over y) P.P) :
    Cong Λ n (x : ℍ[ℚ, a, b]) (y : ℍ[ℚ, a, b]) := by
  classical
  obtain ⟨m, hm⟩ := Ideal.exists_maximal S
  haveI : m.IsMaximal := hm
  letI : Field (S ⧸ m) := Ideal.Quotient.field m
  let k : Type := AlgebraicClosure (S ⧸ m)
  let sk : S →+* k := (algebraMap (S ⧸ m) k).comp (Ideal.Quotient.mk m)
  letI := A.L.pointGroup (geomPoint k sk)
  let i : ↥Λ → SchemeHomOver (geomPoint k sk) A.f → SchemeHomOver (geomPoint k sk) A.f :=
    fun z Q => pushPt (A.act z) (A.act_over z) Q
  let sP : SchemeHomOver (geomPoint k sk) A.f := FakeEllipticCurve.sectionAt P.P k sk
  have hsec : ∀ z : ↥Λ, i z sP = FakeEllipticCurve.sectionAt (pushPt (A.act z) (A.act_over z) P.P) k sk := by
    intro z
    apply Subtype.ext
    simp only [i, sP, FakeEllipticCurve.sectionAt, pushPt, mapPt_coe, GoodReductionJacobian.schemeHomOverComp_coe,
      Category.assoc]
  have hxy : i x sP = i y sP := by rw [hsec, hsec, h]
  have i_add : ∀ (u v : ↥Λ) (Q : SchemeHomOver (geomPoint k sk) A.f), i (u + v) Q = i u Q * i v Q :=
    fun u v Q => A.act_add u v _ Q
  have e : y + (x - y) = x := by abel
  have h1 : i y sP * i (x - y) sP = i y sP * 1 := by
    rw [← i_add, mul_one, congrArg (fun z => i z sP) e, hxy]
  have hw : i (x - y) sP = 1 := mul_left_cancel h1
  obtain ⟨z, hz⟩ := (P.annihilator k sk (x - y)).1 hw
  exact ⟨z, by rw [← Submodule.coe_sub]; exact hz⟩

end Act

end KCHARdd

open KCHARdd in
theorem solution
    {r : ℕ} [Fact r.Prime] {a b a₁ b₁ : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    {N : ℕ} (n : ℕ) [NeZero n] (hrn : ¬ r ∣ n)
    {k₀ : Type} [CommRing k₀] [Nontrivial k₀] {K₀ : Type} [Field K₀] [CharZero K₀]
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (A₀ : FakeEllipticCurve Λ N k₀) (X₀ : FormalODModule r k₀) (θ₀ : RelativeGroupLaw.FormalCoordinates A₀.f 2)
    (hA₀ : A₀.IsFormalModuleVia coord X₀ θ₀)
    (Γt : Subgroup (ℍ[ℚ, a₁, b₁])ˣ) (ι₀ : ℍ[ℚ, a₁, b₁] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) K₀)
    (e : ↥Γt → (A₀.A ⟶ A₀.A)) (he : ∀ γ, e γ ≫ A₀.f = A₀.f)
    (hecomm : ∀ (γ : ↥Γt) (x : ↥Λ), A₀.act x ≫ e γ = e γ ≫ A₀.act x)
    (hE1mul :
      (∀ γ γ' : ↥Γt, ∃ i j : ℕ,
          e (γ * γ') ≫ A₀.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = e γ' ≫ e γ ≫ A₀.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩))
    (P₀ : A₀.FullLevel n)
    (hlab : ∃ lab : ↥Γt → ↥Λ,
        (∀ γ : ↥Γt, mapPt (e γ) (he γ) P₀.P = pushPt (A₀.act (lab γ)) (A₀.act_over (lab γ)) P₀.P) ∧
        (∀ γ γ' : ↥Γt, ∃ y : ↥Λ, (lab (γ * γ') : ℍ[ℚ, a, b]) - (lab γ' : ℍ[ℚ, a, b]) * (lab γ : ℍ[ℚ, a, b]) = (n : ℚ) • (y : ℍ[ℚ, a, b])) ∧
        (∀ (γ : ↥Γt) (c : ℤ), ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) = (c : ℚ) • (1 : ℍ[ℚ, a₁, b₁]) →
            ∃ y : ↥Λ, (lab γ : ℍ[ℚ, a, b]) - (c : ℚ) • (1 : ℍ[ℚ, a, b]) = (n : ℚ) • (y : ℍ[ℚ, a, b])))
    (E : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd})) →+* Matrix (Fin 2) (Fin 2) K₀)
    (g : Matrix.GeneralLinearGroup (Fin 2) K₀)
    (ε : ↥Γt → ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}))) (k : ↥Γt → ℤ)
    (hεk : ∀ γ : ↥Γt,
      (∀ (B' : Type) [CommRing B'] [Algebra k₀ B'] (J : Ideal B') (m : ℕ),
          J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B', (∀ i, s i ∈ J) →
          θ₀ B' (fun i => MvFormalGroup.nilEval m (((ε γ) : MvFormalGroup.End X₀.F).toPowerSeries i) s) =
            mapPt (e γ) (he γ) (θ₀ B' s)) ∧
      E (ε γ) = ((r : K₀) ^ k γ) • ((g : Matrix (Fin 2) (Fin 2) K₀) * ι₀ ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) *
        ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀))) :
    ∃ κ : ↥Γt →* (ZMod n)ˣ,
      ∀ γ : ↥Γt, ((κ γ : (ZMod n)ˣ) : ZMod n) * (r : ZMod n) ^ (-(k γ)).toNat = (r : ZMod n) ^ (k γ).toNat := by
  classical
  obtain ⟨lab, hlabP, hmul, hsc⟩ := hlab
  have hr : r.Prime := Fact.out

  let rI : ℕ → ↥Λ := fun i => ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩
  have rI_coe : ∀ i : ℕ, (rI i : ℍ[ℚ, a, b]) = ((((r ^ i : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b]) := fun i => rfl

  have hone : Cong Λ n (lab 1 : ℍ[ℚ, a, b]) 1 := by
    obtain ⟨y, hy⟩ := hsc 1 1 (by simp)
    have h11 : ((1 : ℤ) : ℚ) • (1 : ℍ[ℚ, a, b]) = 1 := by rw [Int.cast_one, one_smul]
    rw [h11] at hy
    exact ⟨y, hy⟩
  have hinv₂ : ∀ γ : ↥Γt, Cong Λ n ((lab γ : ℍ[ℚ, a, b]) * (lab γ⁻¹ : ℍ[ℚ, a, b])) 1 := by
    intro γ
    obtain ⟨y, hy⟩ := hmul γ⁻¹ γ
    rw [inv_mul_cancel] at hy
    exact (Cong.symm ⟨y, hy⟩).trans hone

  have levelP : ∀ (γ γ' : ↥Γt) (i j : ℕ),
      e (γ * γ') ≫ A₀.act (rI i) = e γ' ≫ e γ ≫ A₀.act (rI j) →
      pushPt (A₀.act ⟨(rI i : ℍ[ℚ, a, b]) * (lab (γ * γ') : ℍ[ℚ, a, b]), hΛ.mul_mem (rI i).2 (lab _).2⟩) (A₀.act_over _) P₀.P =
        pushPt (A₀.act ⟨(rI j : ℍ[ℚ, a, b]) * ((lab γ' : ℍ[ℚ, a, b]) * (lab γ : ℍ[ℚ, a, b])),
          hΛ.mul_mem (rI j).2 (hΛ.mul_mem (lab _).2 (lab _).2)⟩) (A₀.act_over _) P₀.P := by
    intro γ γ' i j hij
    have hlabv : ∀ (δ : ↥Γt) {Z : Scheme.{0}} (φ : A₀.A ⟶ Z), P₀.P.1 ≫ e δ ≫ φ = P₀.P.1 ≫ A₀.act (lab δ) ≫ φ := by
      intro δ Z φ
      have := congrArg Subtype.val (hlabP δ)
      simp only [mapPt_coe] at this
      rw [← Category.assoc, this, Category.assoc]
    have hcommv : ∀ (δ : ↥Γt) (x : ↥Λ) {Z : Scheme.{0}} (φ : A₀.A ⟶ Z),
        A₀.act x ≫ e δ ≫ φ = e δ ≫ A₀.act x ≫ φ := by
      intro δ x Z φ
      rw [← Category.assoc, hecomm, Category.assoc]
    apply Subtype.ext
    simp only [mapPt_coe]
    rw [A₀.act_mul (rI i) (lab (γ * γ')) (hΛ.mul_mem (rI i).2 (lab _).2),
      A₀.act_mul (rI j) ⟨(lab γ' : ℍ[ℚ, a, b]) * (lab γ : ℍ[ℚ, a, b]), hΛ.mul_mem (lab _).2 (lab _).2⟩
        (hΛ.mul_mem (rI j).2 (hΛ.mul_mem (lab _).2 (lab _).2)),
      A₀.act_mul (lab γ') (lab γ) (hΛ.mul_mem (lab _).2 (lab _).2)]
    simp only [Category.assoc]
    rw [← hlabv (γ * γ'), hij, hlabv γ', hcommv γ (lab γ'), hlabv γ]

  have rij_zmod : ∀ (γ γ' : ↥Γt) (i j : ℕ),
      e (γ * γ') ≫ A₀.act (rI i) = e γ' ≫ e γ ≫ A₀.act (rI j) → ((r : ZMod n)) ^ i = ((r : ZMod n)) ^ j := by
    intro γ γ' i j hij
    have c1 := cong_of_pushPt_act_eq A₀ P₀ _ _ (levelP γ γ' i j hij)

    have hWmem : ((lab γ' : ℍ[ℚ, a, b]) * (lab γ : ℍ[ℚ, a, b])) ∈ Λ := hΛ.mul_mem (lab _).2 (lab _).2
    have hVmem : ((lab γ⁻¹ : ℍ[ℚ, a, b]) * (lab γ'⁻¹ : ℍ[ℚ, a, b])) ∈ Λ := hΛ.mul_mem (lab _).2 (lab _).2
    have hWV : Cong Λ n (((lab γ' : ℍ[ℚ, a, b]) * (lab γ : ℍ[ℚ, a, b])) * ((lab γ⁻¹ : ℍ[ℚ, a, b]) * (lab γ'⁻¹ : ℍ[ℚ, a, b]))) 1 := by
      have e1 : ((lab γ' : ℍ[ℚ, a, b]) * (lab γ : ℍ[ℚ, a, b])) * ((lab γ⁻¹ : ℍ[ℚ, a, b]) * (lab γ'⁻¹ : ℍ[ℚ, a, b])) = (lab γ' : ℍ[ℚ, a, b]) * (((lab γ : ℍ[ℚ, a, b]) * (lab γ⁻¹ : ℍ[ℚ, a, b])) * (lab γ'⁻¹ : ℍ[ℚ, a, b])) := by
        simp only [mul_assoc]
      rw [e1]
      refine (Cong.mul hΛ (Cong.refl n (lab γ' : ℍ[ℚ, a, b]))
        (Cong.mul hΛ (hinv₂ γ) (Cong.refl n (lab γ'⁻¹ : ℍ[ℚ, a, b])) (lab _).2 hΛ.one_mem)
        (hΛ.mul_mem (hΛ.mul_mem (lab _).2 (lab _).2) (lab _).2) (lab _).2).trans ?_
      rw [one_mul]
      exact hinv₂ γ'

    have c2 : Cong Λ n ((rI i : ℍ[ℚ, a, b]) * (lab (γ * γ') : ℍ[ℚ, a, b])) ((rI i : ℍ[ℚ, a, b]) * ((lab γ' : ℍ[ℚ, a, b]) * (lab γ : ℍ[ℚ, a, b]))) :=
      Cong.mul hΛ (Cong.refl n _) (hmul γ γ') (lab _).2 (rI i).2
    have c3 : Cong Λ n ((rI i : ℍ[ℚ, a, b]) * ((lab γ' : ℍ[ℚ, a, b]) * (lab γ : ℍ[ℚ, a, b]))) ((rI j : ℍ[ℚ, a, b]) * ((lab γ' : ℍ[ℚ, a, b]) * (lab γ : ℍ[ℚ, a, b]))) := c2.symm.trans c1
    have c4 : Cong Λ n ((rI i : ℍ[ℚ, a, b]) * ((lab γ' : ℍ[ℚ, a, b]) * (lab γ : ℍ[ℚ, a, b])) * ((lab γ⁻¹ : ℍ[ℚ, a, b]) * (lab γ'⁻¹ : ℍ[ℚ, a, b]))) ((rI j : ℍ[ℚ, a, b]) * ((lab γ' : ℍ[ℚ, a, b]) * (lab γ : ℍ[ℚ, a, b])) * ((lab γ⁻¹ : ℍ[ℚ, a, b]) * (lab γ'⁻¹ : ℍ[ℚ, a, b]))) :=
      Cong.mul hΛ c3 (Cong.refl n ((lab γ⁻¹ : ℍ[ℚ, a, b]) * (lab γ'⁻¹ : ℍ[ℚ, a, b]))) hVmem (hΛ.mul_mem (rI j).2 hWmem)
    have c4' : Cong Λ n ((rI i : ℍ[ℚ, a, b]) * (((lab γ' : ℍ[ℚ, a, b]) * (lab γ : ℍ[ℚ, a, b])) * ((lab γ⁻¹ : ℍ[ℚ, a, b]) * (lab γ'⁻¹ : ℍ[ℚ, a, b])))) ((rI j : ℍ[ℚ, a, b]) * (((lab γ' : ℍ[ℚ, a, b]) * (lab γ : ℍ[ℚ, a, b])) * ((lab γ⁻¹ : ℍ[ℚ, a, b]) * (lab γ'⁻¹ : ℍ[ℚ, a, b])))) := by
      simpa only [mul_assoc] using c4
    have c5 : Cong Λ n ((rI i : ℍ[ℚ, a, b]) * (((lab γ' : ℍ[ℚ, a, b]) * (lab γ : ℍ[ℚ, a, b])) * ((lab γ⁻¹ : ℍ[ℚ, a, b]) * (lab γ'⁻¹ : ℍ[ℚ, a, b])))) ((rI i : ℍ[ℚ, a, b]) * 1) :=
      Cong.mul hΛ (Cong.refl n _) hWV (hΛ.mul_mem hWmem hVmem) (rI i).2
    have c6 : Cong Λ n ((rI j : ℍ[ℚ, a, b]) * (((lab γ' : ℍ[ℚ, a, b]) * (lab γ : ℍ[ℚ, a, b])) * ((lab γ⁻¹ : ℍ[ℚ, a, b]) * (lab γ'⁻¹ : ℍ[ℚ, a, b])))) ((rI j : ℍ[ℚ, a, b]) * 1) :=
      Cong.mul hΛ (Cong.refl n _) hWV (hΛ.mul_mem hWmem hVmem) (rI j).2
    have c7 : Cong Λ n ((rI i : ℍ[ℚ, a, b])) ((rI j : ℍ[ℚ, a, b])) := by
      have := (c5.symm.trans c4').trans c6
      simpa only [mul_one] using this
    rw [rI_coe, rI_coe] at c7
    have := zmod_eq_of_cong hΛ _ _ c7
    push_cast at this
    exact this

  have hprod : ∀ (φ ψ : MvFormalGroup.End X₀.F) (u v : A₀.A ⟶ A₀.A) (hu : u ≫ A₀.f = A₀.f) (hv : v ≫ A₀.f = A₀.f),
      (∀ (B' : Type) [CommRing B'] [Algebra k₀ B'] (J : Ideal B') (m : ℕ), J ^ (m + 1) = ⊥ →
        ∀ s : Fin 2 → B', (∀ i, s i ∈ J) →
          θ₀ B' (fun i => MvFormalGroup.nilEval m (φ.toPowerSeries i) s) = mapPt u hu (θ₀ B' s)) →
      (∀ (B' : Type) [CommRing B'] [Algebra k₀ B'] (J : Ideal B') (m : ℕ), J ^ (m + 1) = ⊥ →
        ∀ s : Fin 2 → B', (∀ i, s i ∈ J) →
          θ₀ B' (fun i => MvFormalGroup.nilEval m (ψ.toPowerSeries i) s) = mapPt v hv (θ₀ B' s)) →
      ∀ (B' : Type) [CommRing B'] [Algebra k₀ B'] (J : Ideal B') (m : ℕ), J ^ (m + 1) = ⊥ →
        ∀ s : Fin 2 → B', (∀ i, s i ∈ J) →
          θ₀ B' (fun i => MvFormalGroup.nilEval m ((ψ * φ).toPowerSeries i) s) =
            mapPt (u ≫ v) (by rw [Category.assoc, hv, hu]) (θ₀ B' s) := by
    intro φ ψ u v hu hv hφ hψ B' _ _ J m hJ s hs
    have hsub := MvFormalGroup.nilEval_subst_of_mem J m hJ s hs φ.toPowerSeries φ.constantCoeff_eq_zero
    have e1 : (fun i => MvFormalGroup.nilEval m ((ψ * φ).toPowerSeries i) s) =
        fun i => MvFormalGroup.nilEval m (ψ.toPowerSeries i) (fun j => MvFormalGroup.nilEval m (φ.toPowerSeries j) s) := by
      funext i
      rw [MvFormalGroup.End.toPowerSeries_mul]
      exact (hsub (ψ.toPowerSeries i)).2
    apply Subtype.ext
    rw [e1, hψ B' J m hJ _ (hsub (ψ.toPowerSeries 0)).1, hφ B' J m hJ s hs]
    simp only [mapPt_coe, Category.assoc]

  have hnat : ∀ (i : ℕ) (B' : Type) [CommRing B'] [Algebra k₀ B'] (J : Ideal B') (m : ℕ), J ^ (m + 1) = ⊥ →
      ∀ s : Fin 2 → B', (∀ l, s l ∈ J) →
        θ₀ B' (fun l => MvFormalGroup.nilEval m ((((r ^ i : ℕ) : MvFormalGroup.End X₀.F)).toPowerSeries l) s) =
          mapPt (A₀.act (rI i)) (A₀.act_over _) (θ₀ B' s) := by
    intro i B' _ _ J m hJ s hs
    have hn : (((r ^ i : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
      have := hΛℤ ((r ^ i : ℕ) : ℤ)
      rwa [Int.cast_natCast] at this
    have h := CerednikDrinfeld.QM.FakeEllipticCurve.apply_nilEval_natCast_eq_mapPt_act_of_isFormalModuleVia
      A₀ coord hcoord X₀ θ₀ hA₀ hΛ.one_mem (r ^ i) hn B' J m hJ s hs
    have hel : (⟨(((r ^ i : ℕ) : ℕ) : ℚ), hn⟩ : ↥Λ) = rI i := by
      apply Subtype.ext
      show (((r ^ i : ℕ) : ℚ) : ℍ[ℚ, a, b]) = ((((r ^ i : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b])
      rw [Int.cast_natCast]
    rw [h]
    exact pushPt_act_congr A₀ hel _

  have germ_id : ∀ (γ γ' : ↥Γt) (i j : ℕ),
      e (γ * γ') ≫ A₀.act (rI i) = e γ' ≫ e γ ≫ A₀.act (rI j) →
      ((r ^ i : ℕ) : MvFormalGroup.End X₀.F) * (ε (γ * γ') : MvFormalGroup.End X₀.F) =
        ((r ^ j : ℕ) : MvFormalGroup.End X₀.F) * (ε γ : MvFormalGroup.End X₀.F) * (ε γ' : MvFormalGroup.End X₀.F) := by
    intro γ γ' i j hij
    have hL := hprod (ε (γ * γ') : MvFormalGroup.End X₀.F) ((r ^ i : ℕ) : MvFormalGroup.End X₀.F)
      (e (γ * γ')) (A₀.act (rI i)) (he _) (A₀.act_over _) (hεk (γ * γ')).1 (hnat i)
    have hR₁ := hprod (ε γ : MvFormalGroup.End X₀.F) ((r ^ j : ℕ) : MvFormalGroup.End X₀.F)
      (e γ) (A₀.act (rI j)) (he _) (A₀.act_over _) (hεk γ).1 (hnat j)
    have hR := hprod (ε γ' : MvFormalGroup.End X₀.F) (((r ^ j : ℕ) : MvFormalGroup.End X₀.F) * (ε γ : MvFormalGroup.End X₀.F))
      (e γ') (e γ ≫ A₀.act (rI j)) (he _) (by rw [Category.assoc, A₀.act_over, he]) (hεk γ').1 hR₁
    apply GoodReductionJacobian.RelativeGroupLaw.IsFormalCoordinates.eq_of_forall_apply_nilEval_eq A₀.L X₀.F θ₀ hA₀.1
    intro B' _ _ J m hJ s hs
    rw [hL B' J m hJ s hs, hR B' J m hJ s hs]
    apply Subtype.ext
    simp only [mapPt_coe]
    rw [hij]

  have hr0 : (r : K₀) ≠ 0 := by exact_mod_cast hr.ne_zero
  set G : Matrix (Fin 2) (Fin 2) K₀ := (g : Matrix (Fin 2) (Fin 2) K₀) with hG
  set Gi : Matrix (Fin 2) (Fin 2) K₀ := ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀) with hGi
  have hGiG : Gi * G = 1 := by simp only [hG, hGi]; exact Units.inv_mul g
  have hGGi : G * Gi = 1 := by simp only [hG, hGi]; exact Units.mul_inv g
  let I : ↥Γt → Matrix (Fin 2) (Fin 2) K₀ := fun γ => ι₀ ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁])
  have hImul : ∀ γ γ' : ↥Γt, I (γ * γ') = I γ * I γ' := by
    intro γ γ'
    simp only [I, Subgroup.coe_mul, Units.val_mul, map_mul]
  have hIinv : ∀ γ : ↥Γt, I γ * I γ⁻¹ = 1 := by
    intro γ
    rw [← hImul, mul_inv_cancel]
    simp only [I, Subgroup.coe_one, Units.val_one, map_one]
  have hEγ : ∀ γ : ↥Γt, E (ε γ) = ((r : K₀) ^ k γ) • (G * I γ * Gi) := fun γ => (hεk γ).2
  have natmul : ∀ (l : ℕ) (M : Matrix (Fin 2) (Fin 2) K₀), (l : Matrix (Fin 2) (Fin 2) K₀) * M = (l : K₀) • M := by
    intro l M
    rw [← nsmul_eq_mul, Nat.cast_smul_eq_nsmul]
  have kadd : ∀ (γ γ' : ↥Γt) (i j : ℕ),
      e (γ * γ') ≫ A₀.act (rI i) = e γ' ≫ e γ ≫ A₀.act (rI j) → (i : ℤ) + k (γ * γ') = (j : ℤ) + k γ + k γ' := by
    intro γ γ' i j hij
    have h0 := germ_id γ γ' i j hij

    have h1 : ((r ^ i : ℕ) : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}))) * ε (γ * γ') =
        ((r ^ j : ℕ) : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}))) * ε γ * ε γ' := by
      apply Subtype.ext
      push_cast at h0 ⊢
      exact h0
    have h2 := congrArg E h1
    rw [map_mul, map_mul, map_mul, map_natCast, map_natCast, hEγ, hEγ, hEγ, natmul, natmul] at h2

    have hM : (G * I γ * Gi) * (G * I γ' * Gi) = G * I (γ * γ') * Gi := by
      calc (G * I γ * Gi) * (G * I γ' * Gi) = G * I γ * (Gi * G) * I γ' * Gi := by simp only [mul_assoc]
        _ = G * I (γ * γ') * Gi := by rw [hGiG, mul_one, hImul]; simp only [mul_assoc]
    have h3 : ((((r ^ i : ℕ) : ℕ) : K₀) * (r : K₀) ^ k (γ * γ')) • (G * I (γ * γ') * Gi) =
        ((((r ^ j : ℕ) : ℕ) : K₀) * (r : K₀) ^ k γ * (r : K₀) ^ k γ') • (G * I (γ * γ') * Gi) := by
      rw [smul_smul] at h2
      rw [h2, ← hM]
      simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc]
      congr 1
      ring

    have hunit : (G * I (γ * γ') * Gi) * (G * I (γ * γ')⁻¹ * Gi) = 1 := by
      calc (G * I (γ * γ') * Gi) * (G * I (γ * γ')⁻¹ * Gi) = G * (I (γ * γ') * ((Gi * G) * I (γ * γ')⁻¹)) * Gi := by
            simp only [mul_assoc]
        _ = 1 := by rw [hGiG, one_mul, hIinv, mul_one, hGGi]
    have h4 := congrArg (fun X => X * (G * I (γ * γ')⁻¹ * Gi)) h3
    simp only [smul_mul_assoc, hunit] at h4
    have h5 : (((r ^ i : ℕ) : ℕ) : K₀) * (r : K₀) ^ k (γ * γ') = (((r ^ j : ℕ) : ℕ) : K₀) * (r : K₀) ^ k γ * (r : K₀) ^ k γ' := by
      have := congrArg (fun X : Matrix (Fin 2) (Fin 2) K₀ => X 0 0) h4
      simpa using this

    have h6 : (r : K₀) ^ ((i : ℤ) + k (γ * γ')) = (r : K₀) ^ ((j : ℤ) + k γ + k γ') := by
      rw [zpow_add₀ hr0, zpow_add₀ hr0, zpow_add₀ hr0, zpow_natCast, zpow_natCast]
      push_cast at h5
      exact h5
    have h7 : ((r : ℚ) : K₀) ^ ((i : ℤ) + k (γ * γ')) = ((r : ℚ) : K₀) ^ ((j : ℤ) + k γ + k γ') := by
      rw [Rat.cast_natCast]; exact h6
    rw [← Rat.cast_zpow, ← Rat.cast_zpow] at h7
    have h8 : (r : ℚ) ^ ((i : ℤ) + k (γ * γ')) = (r : ℚ) ^ ((j : ℤ) + k γ + k γ') := Rat.cast_injective h7
    exact zpow_right_injective₀ (by exact_mod_cast hr.pos) (by exact_mod_cast hr.one_lt.ne') h8

  have hcop : r.Coprime n := (Nat.Prime.coprime_iff_not_dvd hr).mpr hrn
  let u : (ZMod n)ˣ := ZMod.unitOfCoprime r hcop
  have hu : (u : ZMod n) = (r : ZMod n) := ZMod.coe_unitOfCoprime r hcop
  have upow : ∀ (i j : ℕ), ((r : ZMod n)) ^ i = ((r : ZMod n)) ^ j → u ^ (i : ℤ) = u ^ (j : ℤ) := by
    intro i j h
    rw [zpow_natCast, zpow_natCast]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hu]
    exact h
  have hmulκ : ∀ γ γ' : ↥Γt, u ^ k (γ * γ') = u ^ k γ * u ^ k γ' := by
    intro γ γ'
    obtain ⟨i, j, hij⟩ := hE1mul γ γ'
    have h1 := kadd γ γ' i j hij
    have h2 := upow i j (rij_zmod γ γ' i j hij)
    have : k (γ * γ') = k γ + k γ' + ((j : ℤ) - (i : ℤ)) := by linarith
    rw [this, zpow_add, zpow_add, zpow_sub, h2, mul_inv_cancel, mul_one]
  let κ : ↥Γt →* (ZMod n)ˣ := MonoidHom.mk' (fun γ => u ^ k γ) hmulκ
  refine ⟨κ, fun γ => ?_⟩
  show ((u ^ k γ : (ZMod n)ˣ) : ZMod n) * (r : ZMod n) ^ (-(k γ)).toNat = (r : ZMod n) ^ (k γ).toNat
  obtain ⟨m, hm | hm⟩ := Int.eq_nat_or_neg (k γ)
  · rw [hm]
    simp only [Int.toNat_natCast, Int.toNat_neg_natCast, pow_zero, mul_one, zpow_natCast, Units.val_pow_eq_pow_val, hu]
  · rw [hm, neg_neg]
    simp only [Int.toNat_natCast, Int.toNat_neg_natCast, pow_zero, zpow_neg, zpow_natCast]
    rw [← hu, ← Units.val_pow_eq_pow_val, Units.inv_mul]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_monoidHom_units_zmod_eq_pow_of_endomorphismDictionary_slack_of_comm
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_monoidHom_units_zmod_eq_pow_of_endomorphismDictionary_slack_of_comm (solution)
