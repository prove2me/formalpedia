-- Prove2me | solution 1 for CohCarrier.exists_atkinLehnerOp_iDegL_jDegL_five_identities_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/b2831aa4-e386-561e-b8a4-2ab1b121acfc

import Mathlib
import Definitions.Def_CohCarrier_Level
import Definitions.Def_CohCarrier_Lower
import Definitions.Def_CohCarrier_Inst
import Theorems.Thm_CohCarrier_exists_gamma0_heckeT_iDeg_interchange_diamondRaw
import Theorems.Thm_CohCarrier_exists_gamma0_heckeTlower_eq_heckeT_diamondRaw
import Theorems.Thm_CohCarrier_jDeg_iDeg_cross_eq_index_smul_heckeTlower
import Theorems.Thm_CohCarrier_jDeg_comp_iDegP_self
import Theorems.Thm_CohCarrier_index_GammaHUpper_of_prime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_exists_atkinLehnerOp_iDegL_jDegL_five_identities_of_prime
p2m_attr_erase "simp" "CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace AtkinLehnerH1Sol

open MulAction

section SectionFormula

variable {G : Type*} [Group G] {H : Subgroup G} {C : Type*} [CommGroup C]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

theorem mem_of_section {f : G ⧸ H → G} (hf : ∀ q, (f q : G ⧸ H) = q) (g : G) (q : G ⧸ H) :
    (f q)⁻¹ * (g * f (g⁻¹ • q)) ∈ H := by
  rw [← QuotientGroup.eq, hf q, ← smul_eq_mul, ← MulAction.Quotient.smul_coe, hf, smul_inv_smul]

theorem transfer_eq_prod_section [H.FiniteIndex] (χ : H →* C) (f : G ⧸ H → G)
    (hf : ∀ q, (f q : G ⧸ H) = q) (g : G) :
    MonoidHom.transfer χ g
      = ∏ q : G ⧸ H, χ ⟨(f q)⁻¹ * (g * f (g⁻¹ • q)), mem_of_section hf g q⟩ := by
  let T : H.LeftTransversal := ⟨Set.range f, Subgroup.isComplement_range_left hf⟩
  rw [MonoidHom.transfer_def χ T g]
  unfold Subgroup.leftTransversals.diff
  refine Finset.prod_congr rfl (fun q _ => congrArg χ (Subtype.ext ?_))
  simp only [Subgroup.smul_apply_eq_smul_apply_inv_smul, smul_eq_mul, T,
    Subgroup.IsComplement.leftQuotientEquiv_apply hf]

end SectionFormula

section Naturality

variable {G G₂ : Type*} [Group G] [Group G₂] {C : Type*} [CommGroup C]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

def restrictEquiv (e : G ≃* G₂) (H : Subgroup G) (H₂ : Subgroup G₂)
    (hH : ∀ x, x ∈ H ↔ e x ∈ H₂) : H →* H₂ :=
  (e.toMonoidHom.domRestrict H).codRestrict H₂ (fun x => (hH x).mp x.2)

@[scoped simp] theorem coe_restrictEquiv (e : G ≃* G₂) (H : Subgroup G) (H₂ : Subgroup G₂)
    (hH : ∀ x, x ∈ H ↔ e x ∈ H₂) (x : H) : (restrictEquiv e H H₂ hH x : G₂) = e x := rfl

noncomputable def quotEquiv (e : G ≃* G₂) (H : Subgroup G) (H₂ : Subgroup G₂)
    (hH : ∀ x, x ∈ H ↔ e x ∈ H₂) : G ⧸ H ≃ G₂ ⧸ H₂ :=
  Equiv.ofBijective
    (Quotient.map' e (fun x y hxy => by
      rw [QuotientGroup.leftRel_apply] at hxy ⊢
      rw [← map_inv, ← map_mul]
      exact (hH _).mp hxy))
    ⟨by
      intro a b
      induction a using Quotient.inductionOn' with | h a => ?_
      induction b using Quotient.inductionOn' with | h b => ?_
      intro hab
      change (QuotientGroup.mk (e a) : G₂ ⧸ H₂) = QuotientGroup.mk (e b) at hab
      change (QuotientGroup.mk a : G ⧸ H) = QuotientGroup.mk b
      rw [QuotientGroup.eq] at hab ⊢
      rw [← map_inv, ← map_mul] at hab
      exact (hH _).mpr hab,
     by
      intro b
      induction b using Quotient.inductionOn' with | h b => ?_
      exact ⟨QuotientGroup.mk (e.symm b), by
        change (QuotientGroup.mk (e (e.symm b)) : G₂ ⧸ H₂) = _
        rw [MulEquiv.apply_symm_apply]⟩⟩

theorem quotEquiv_mk (e : G ≃* G₂) (H : Subgroup G) (H₂ : Subgroup G₂)
    (hH : ∀ x, x ∈ H ↔ e x ∈ H₂) (a : G) :
    quotEquiv e H H₂ hH (QuotientGroup.mk a) = QuotientGroup.mk (e a) := rfl

theorem quotEquiv_smul (e : G ≃* G₂) (H : Subgroup G) (H₂ : Subgroup G₂)
    (hH : ∀ x, x ∈ H ↔ e x ∈ H₂) (g : G) (q : G ⧸ H) :
    quotEquiv e H H₂ hH (g • q) = e g • quotEquiv e H H₂ hH q := by
  induction q using Quotient.inductionOn' with | h a => ?_
  change quotEquiv e H H₂ hH (g • QuotientGroup.mk a) = e g • quotEquiv e H H₂ hH (QuotientGroup.mk a)
  rw [MulAction.Quotient.smul_mk, quotEquiv_mk, quotEquiv_mk, MulAction.Quotient.smul_mk,
    smul_eq_mul, smul_eq_mul, map_mul]

theorem transfer_comp_equiv (e : G ≃* G₂) (H : Subgroup G) (H₂ : Subgroup G₂)
    [H.FiniteIndex] [H₂.FiniteIndex]
    (hH : ∀ x, x ∈ H ↔ e x ∈ H₂) (χ : H₂ →* C) (g : G) :
    MonoidHom.transfer (χ.comp (restrictEquiv e H H₂ hH)) g = MonoidHom.transfer χ (e g) := by
  set Q := quotEquiv e H H₂ hH with hQ
  have hQs : ∀ (a : G) (q : G ⧸ H), Q (a • q) = e a • Q q := fun a q => by
    rw [hQ]; exact quotEquiv_smul e H H₂ hH a q
  let f₂ : G₂ ⧸ H₂ → G₂ := Quotient.out
  have hf₂ : ∀ q, (f₂ q : G₂ ⧸ H₂) = q := fun q => Quotient.out_eq q
  let f : G ⧸ H → G := fun q => e.symm (f₂ (Q q))
  have hf : ∀ q, (f q : G ⧸ H) = q := by
    intro q
    apply Q.injective
    induction q using Quotient.inductionOn' with | h a => ?_
    change Q (QuotientGroup.mk (e.symm (f₂ (Q _)))) = _
    rw [quotEquiv_mk, MulEquiv.apply_symm_apply]
    exact hf₂ _
  rw [transfer_eq_prod_section _ f hf, transfer_eq_prod_section _ f₂ hf₂,
    ← Fintype.prod_equiv Q.symm _ _ (fun _ => rfl)]
  refine Finset.prod_congr rfl (fun q _ => ?_)
  rw [MonoidHom.comp_apply]
  refine congrArg χ (Subtype.ext ?_)
  simp only [coe_restrictEquiv, map_mul, map_inv, f, MulEquiv.apply_symm_apply,
    Equiv.apply_symm_apply]
  congr 3
  rw [hQs, map_inv, Q.apply_symm_apply]

theorem mem_iff_of_forall_mem (e : G ≃* G) (H : Subgroup G) [H.FiniteIndex]
    (h : ∀ x ∈ H, e x ∈ H) (x : G) : x ∈ H ↔ e x ∈ H := by
  have hle : H ≤ H.comap e.toMonoidHom := fun y hy => h y hy
  have hidx : (H.comap e.toMonoidHom).index = H.index :=
    H.index_comap_of_surjective (f := e.toMonoidHom) e.surjective
  have hrel := Subgroup.relIndex_mul_index hle
  rw [hidx] at hrel
  have hone : H.relIndex (H.comap e.toMonoidHom) = 1 := by
    have hne : H.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
    have := hrel
    nth_rewrite 2 [← one_mul H.index] at this
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hne) this
  have hge : H.comap e.toMonoidHom ≤ H := Subgroup.relIndex_eq_one.mp hone
  exact ⟨fun hx => h x hx, fun hx => hge hx⟩

end Naturality

section Mackey

variable {G : Type*} [Group G] {C : Type*} [CommGroup C]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

def conjChar (R : Subgroup G) (w : G) (Kw : Subgroup R)
    (hKw : ∀ l : R, l ∈ Kw ↔ w⁻¹ * (l : G) * w ∈ R) (χ : R →* C) : Kw →* C where
  toFun k := χ ⟨w⁻¹ * ((k : R) : G) * w, (hKw k).mp k.2⟩
  map_one' := by
    have : (⟨w⁻¹ * (((1 : Kw) : R) : G) * w, (hKw (1 : Kw)).mp (1 : Kw).2⟩ : R) = 1 :=
      Subtype.ext (by simp)
    rw [this, map_one]
  map_mul' k k' := by
    rw [← map_mul]
    exact congrArg χ (Subtype.ext (by simp only [Subgroup.coe_mul]; group))

@[scoped simp] theorem conjChar_apply (R : Subgroup G) (w : G) (Kw : Subgroup R)
    (hKw : ∀ l : R, l ∈ Kw ↔ w⁻¹ * (l : G) * w ∈ R) (χ : R →* C) (k : Kw) :
    conjChar R w Kw hKw χ k = χ ⟨w⁻¹ * ((k : R) : G) * w, (hKw k).mp k.2⟩ := rfl

def optMap (R : Subgroup G) (w : G) (Kw : Subgroup R)
    (hKw : ∀ l : R, l ∈ Kw ↔ w⁻¹ * (l : G) * w ∈ R) : Option (R ⧸ Kw) → G ⧸ R :=
  fun o => o.elim (QuotientGroup.mk 1)
    (Quotient.map' (fun x : R => (x : G) * w) (fun x y hxy => by
      rw [QuotientGroup.leftRel_apply] at hxy ⊢
      have h := (hKw _).mp hxy
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, mul_assoc] using h))

theorem optMap_none (R : Subgroup G) (w : G) (Kw : Subgroup R)
    (hKw : ∀ l : R, l ∈ Kw ↔ w⁻¹ * (l : G) * w ∈ R) :
    optMap R w Kw hKw none = QuotientGroup.mk 1 := rfl

theorem optMap_some_mk (R : Subgroup G) (w : G) (Kw : Subgroup R)
    (hKw : ∀ l : R, l ∈ Kw ↔ w⁻¹ * (l : G) * w ∈ R) (x : R) :
    optMap R w Kw hKw (some (QuotientGroup.mk x)) = QuotientGroup.mk ((x : G) * w) := rfl

theorem optMap_some_smul (R : Subgroup G) (w : G) (Kw : Subgroup R)
    (hKw : ∀ l : R, l ∈ Kw ↔ w⁻¹ * (l : G) * w ∈ R) (y : R) (p : R ⧸ Kw) :
    optMap R w Kw hKw (some (y • p)) = (y : G) • optMap R w Kw hKw (some p) := by
  induction p using Quotient.inductionOn' with | h a => ?_
  change optMap R w Kw hKw (some (y • QuotientGroup.mk a)) =
    (y : G) • optMap R w Kw hKw (some (QuotientGroup.mk a))
  rw [MulAction.Quotient.smul_mk, optMap_some_mk, optMap_some_mk, MulAction.Quotient.smul_mk,
    smul_eq_mul, smul_eq_mul, Subgroup.coe_mul, mul_assoc]

theorem optMap_bijective (R : Subgroup G) (w : G) (Kw : Subgroup R)
    (hKw : ∀ l : R, l ∈ Kw ↔ w⁻¹ * (l : G) * w ∈ R)
    (hdec : ∀ g : G, g ∈ R ∨ ∃ l ∈ R, w⁻¹ * (l⁻¹ * g) ∈ R)
    (hnot : w ∉ R) :
    Function.Bijective (optMap R w Kw hKw) := by
  constructor
  · rintro (_ | a) (_ | b) hab
    · rfl
    · exfalso
      induction b using Quotient.inductionOn' with | h b => ?_
      change (QuotientGroup.mk 1 : G ⧸ R) = QuotientGroup.mk ((b : G) * w) at hab
      rw [QuotientGroup.eq, inv_one, one_mul] at hab
      exact hnot (by simpa using R.mul_mem (R.inv_mem b.2) hab)
    · exfalso
      induction a using Quotient.inductionOn' with | h a => ?_
      change QuotientGroup.mk ((a : G) * w) = (QuotientGroup.mk 1 : G ⧸ R) at hab
      rw [eq_comm, QuotientGroup.eq, inv_one, one_mul] at hab
      exact hnot (by simpa using R.mul_mem (R.inv_mem a.2) hab)
    · induction a using Quotient.inductionOn' with | h a => ?_
      induction b using Quotient.inductionOn' with | h b => ?_
      change QuotientGroup.mk ((a : G) * w) = (QuotientGroup.mk ((b : G) * w) : G ⧸ R) at hab
      rw [QuotientGroup.eq] at hab
      change some (QuotientGroup.mk a : R ⧸ Kw) = some (QuotientGroup.mk b)
      rw [Option.some_inj, QuotientGroup.eq, hKw, Subgroup.coe_mul, Subgroup.coe_inv]
      simpa only [mul_inv_rev, mul_assoc] using hab
  · intro Q
    induction Q using Quotient.inductionOn' with | h g => ?_
    rcases hdec g with hg | ⟨l, hl, hlg⟩
    · exact ⟨none, by
        change (QuotientGroup.mk 1 : G ⧸ R) = QuotientGroup.mk g
        rw [QuotientGroup.eq, inv_one, one_mul]; exact hg⟩
    · exact ⟨some (QuotientGroup.mk ⟨l, hl⟩), by
        change (QuotientGroup.mk (l * w) : G ⧸ R) = QuotientGroup.mk g
        rw [QuotientGroup.eq, mul_inv_rev, mul_assoc]; exact hlg⟩

theorem transfer_mackey_self (R : Subgroup G) [R.FiniteIndex] (w : G) (Kw : Subgroup R)
    [Kw.FiniteIndex] (hKw : ∀ l : R, l ∈ Kw ↔ w⁻¹ * (l : G) * w ∈ R)
    (hdec : ∀ g : G, g ∈ R ∨ ∃ l ∈ R, w⁻¹ * (l⁻¹ * g) ∈ R)
    (hnot : w ∉ R) (χ : R →* C) (y : R) :
    MonoidHom.transfer χ (y : G) = χ y * MonoidHom.transfer (conjChar R w Kw hKw χ) y := by
  set E : Option (R ⧸ Kw) ≃ G ⧸ R :=
    Equiv.ofBijective (optMap R w Kw hKw) (optMap_bijective R w Kw hKw hdec hnot) with hE
  have hEa : ∀ o, E o = optMap R w Kw hKw o := fun o => rfl

  let s : R ⧸ Kw → R := Quotient.out
  have hs : ∀ p, (s p : R ⧸ Kw) = p := fun p => Quotient.out_eq p
  let f : G ⧸ R → G := fun Q => (E.symm Q).elim 1 (fun p => (s p : G) * w)
  have hf : ∀ Q, (f Q : G ⧸ R) = Q := by
    intro Q
    obtain ⟨o, rfl⟩ := E.surjective Q
    simp only [f, Equiv.symm_apply_apply]
    cases o with
    | none => rfl
    | some p =>
        change QuotientGroup.mk ((s p : G) * w) = E (some p)
        rw [hEa]
        conv_rhs => rw [← hs p]
        rfl
  rw [transfer_eq_prod_section χ f hf, transfer_eq_prod_section _ s hs,
    ← Fintype.prod_equiv E _ _ (fun _ => rfl), Fintype.prod_option]
  congr 1
  · refine congrArg χ (Subtype.ext ?_)
    have h1 : (y : G)⁻¹ • E none = E none := by
      rw [hEa, optMap_none, MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq]
      simp only [mul_one, inv_inv]
      exact y.2
    simp only [f, h1, Equiv.symm_apply_apply, Option.elim, inv_one, one_mul, mul_one]
  · refine Finset.prod_congr rfl (fun p _ => ?_)
    rw [conjChar_apply]
    refine congrArg χ (Subtype.ext ?_)
    have h1 : (y : G)⁻¹ • E (some p) = E (some (y⁻¹ • p)) := by
      rw [hEa, hEa, optMap_some_smul, Subgroup.coe_inv]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, f, h1, Equiv.symm_apply_apply, Option.elim,
      mul_inv_rev, mul_assoc]

end Mackey

section GLQ

open Matrix
open scoped MatrixGroups

noncomputable abbrev toGLQ : SL(2, ℤ) →* GL (Fin 2) ℚ := Matrix.SpecialLinearGroup.mapGL ℚ

theorem toGLQ_injective : Function.Injective toGLQ := Matrix.SpecialLinearGroup.mapGL_injective

@[scoped simp] theorem toGLQ_apply (A : SL(2, ℤ)) (i j : Fin 2) :
    ((toGLQ A : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) i j = ((A i j : ℤ) : ℚ) := by
  simp [Matrix.SpecialLinearGroup.mapGL_coe_matrix]

def dMat (q : ℕ) [NeZero q] : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(q : ℚ), 0; 0, 1]
    (by rw [Matrix.det_fin_two_of]; simp [NeZero.ne q])

def aMat (ℓ : ℕ) [NeZero ℓ] : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; 0, (ℓ : ℚ)]
    (by rw [Matrix.det_fin_two_of]; simp [NeZero.ne ℓ])

def zMat (q : ℕ) [NeZero q] : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(q : ℚ), 0; 0, (q : ℚ)]
    (by rw [Matrix.det_fin_two_of]; simp [NeZero.ne q])

@[scoped simp] theorem dMat_val (q : ℕ) [NeZero q] :
    ((dMat q : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = !![(q : ℚ), 0; 0, 1] := rfl
@[scoped simp] theorem aMat_val (ℓ : ℕ) [NeZero ℓ] :
    ((aMat ℓ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = !![1, 0; 0, (ℓ : ℚ)] := rfl
@[scoped simp] theorem zMat_val (q : ℕ) [NeZero q] :
    ((zMat q : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = !![(q : ℚ), 0; 0, (q : ℚ)] := rfl

theorem GL_mul_apply (X Y : GL (Fin 2) ℚ) (i j : Fin 2) :
    ((X * Y : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) i j =
      (X : Matrix (Fin 2) (Fin 2) ℚ) i 0 * (Y : Matrix (Fin 2) (Fin 2) ℚ) 0 j +
        (X : Matrix (Fin 2) (Fin 2) ℚ) i 1 * (Y : Matrix (Fin 2) (Fin 2) ℚ) 1 j := by
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem zMat_comm (q : ℕ) [NeZero q] (X : GL (Fin 2) ℚ) : zMat q * X = X * zMat q := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [GL_mul_apply] <;> ring

theorem aMat_dMat_comm (q ℓ : ℕ) [NeZero q] [NeZero ℓ] : aMat ℓ * dMat q = dMat q * aMat ℓ := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [GL_mul_apply]

theorem toGLQ_conjLowerMat (q : ℕ) [NeZero q] (A : SL(2, ℤ)) (h : (q : ℤ) ∣ A 1 0) :
    toGLQ (CohCarrier.conjLowerMat q A h) = dMat q * toGLQ A * (dMat q)⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq]
  have hq : (q : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hq' : ((q : ℤ) : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne q
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [GL_mul_apply, CohCarrier.conjLowerMat, Int.cast_div h hq']
  all_goals ring

theorem toGLQ_conjUpperMat (ℓ : ℕ) [NeZero ℓ] (A : SL(2, ℤ)) (h : (ℓ : ℤ) ∣ A 0 1) :
    toGLQ (CohCarrier.conjUpperMat ℓ A h) = aMat ℓ * toGLQ A * (aMat ℓ)⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq]
  have hℓ : (ℓ : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne ℓ
  have hℓ' : ((ℓ : ℤ) : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne ℓ
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [GL_mul_apply, CohCarrier.conjUpperMat, Int.cast_div h hℓ']
  all_goals ring

end GLQ

section Matrices

open CohCarrier CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups

theorem mul_apply' (x y : SL(2, ℤ)) (i j : Fin 2) :
    (x * y : SL(2, ℤ)) i j = x i 0 * y 0 j + x i 1 * y 1 j := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem inv_apply' (x : SL(2, ℤ)) :
    (x⁻¹ : SL(2, ℤ)) 0 0 = x 1 1 ∧ (x⁻¹ : SL(2, ℤ)) 0 1 = -x 0 1 ∧
      (x⁻¹ : SL(2, ℤ)) 1 0 = -x 1 0 ∧ (x⁻¹ : SL(2, ℤ)) 1 1 = x 0 0 := by
  simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

theorem det_eq' (x : SL(2, ℤ)) : x 0 0 * x 1 1 - x 0 1 * x 1 0 = 1 := by
  have h := Matrix.SpecialLinearGroup.det_coe x
  rw [Matrix.det_fin_two] at h
  exact h

theorem mul_dvd_of_coprime {M q : ℕ} (hcop : IsCoprime (M : ℤ) (q : ℤ)) {z : ℤ}
    (hM : (M : ℤ) ∣ z) (hq : (q : ℤ) ∣ z) : ((M * q : ℕ) : ℤ) ∣ z := by
  push_cast
  exact hcop.mul_dvd hM hq

variable (M q : ℕ)

structure IsAL (t : SL(2, ℤ)) : Prop where
  c_dvd : (M : ℤ) ∣ t 1 0
  d_one : ((t 1 1 : ℤ) : ZMod M) = 1
  d_dvd : (q : ℤ) ∣ t 1 1

variable {M q}

namespace IsAL

variable {t : SL(2, ℤ)}

theorem c_zero (ht : IsAL M q t) : ((t 1 0 : ℤ) : ZMod M) = 0 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ht.c_dvd

theorem a_one (ht : IsAL M q t) : ((t 0 0 : ℤ) : ZMod M) = 1 := by
  have h := congrArg (fun z : ℤ => (z : ZMod M)) (det_eq' t)
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_one, ht.d_one, ht.c_zero, mul_one,
    mul_zero, sub_zero] at h
  exact h

theorem mem_Gamma0 (ht : IsAL M q t) : t ∈ Gamma0 M := by
  rw [Gamma0_mem]; exact ht.c_zero

theorem gamma0Units_eq_one (ht : IsAL M q t) : gamma0Units M ⟨t, ht.mem_Gamma0⟩ = 1 := by
  apply Units.ext
  rw [val_gamma0Units, Units.val_one]
  exact ht.d_one

theorem mem_GammaH (ht : IsAL M q t) (H : Subgroup (ZMod M)ˣ) : t ∈ GammaH M H :=
  mem_GammaH_iff.mpr ⟨ht.mem_Gamma0, by rw [ht.gamma0Units_eq_one]; exact H.one_mem⟩

theorem not_dvd_c (ht : IsAL M q t) (hq : q.Prime) : ¬ (q : ℤ) ∣ t 1 0 := by
  intro hc
  have h1 : (q : ℤ) ∣ 1 := by
    rw [← det_eq' t]
    exact dvd_sub (dvd_mul_of_dvd_right ht.d_dvd _) (dvd_mul_of_dvd_right hc _)
  have := Int.eq_one_of_dvd_one (Int.natCast_nonneg q) h1
  exact hq.one_lt.ne' (by exact_mod_cast this)

theorem conj_10 (x : SL(2, ℤ)) :
    (t * x * t⁻¹ : SL(2, ℤ)) 1 0 =
      t 1 0 * t 1 1 * x 0 0 + t 1 1 ^ 2 * x 1 0 - t 1 0 ^ 2 * x 0 1 - t 1 0 * t 1 1 * x 1 1 := by
  rw [mul_apply', mul_apply', mul_apply', (inv_apply' t).1, (inv_apply' t).2.2.1]
  ring

theorem conj_11 (x : SL(2, ℤ)) :
    (t * x * t⁻¹ : SL(2, ℤ)) 1 1 =
      -(t 0 1 * (t 1 0 * x 0 0 + t 1 1 * x 1 0)) + t 0 0 * (t 1 0 * x 0 1 + t 1 1 * x 1 1) := by
  rw [mul_apply', mul_apply', mul_apply', (inv_apply' t).2.1, (inv_apply' t).2.2.2]
  ring

theorem conj_inv_01 (y : SL(2, ℤ)) :
    (t⁻¹ * y * t : SL(2, ℤ)) 0 1 =
      (t 1 1 * y 0 0 - t 0 1 * y 1 0) * t 0 1 + (t 1 1 * y 0 1 - t 0 1 * y 1 1) * t 1 1 := by
  rw [mul_apply', mul_apply', mul_apply', (inv_apply' t).1, (inv_apply' t).2.1]
  ring

theorem conj_mem_Gamma0 (ht : IsAL M q t) (hcop : IsCoprime (M : ℤ) (q : ℤ)) (x : SL(2, ℤ))
    (hxM : (M : ℤ) ∣ x 1 0) (hxq : (q : ℤ) ∣ x 0 1) : t * x * t⁻¹ ∈ Gamma0 (M * q) := by
  rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd, conj_10]
  apply mul_dvd_of_coprime hcop
  · obtain ⟨c', hc'⟩ := ht.c_dvd
    obtain ⟨x', hx'⟩ := hxM
    rw [hc', hx']
    exact Dvd.intro (c' * t 1 1 * x 0 0 + t 1 1 ^ 2 * x' - M * c' ^ 2 * x 0 1 - c' * t 1 1 * x 1 1)
      (by ring)
  · obtain ⟨d', hd'⟩ := ht.d_dvd
    obtain ⟨x', hx'⟩ := hxq
    rw [hd', hx']
    exact Dvd.intro (t 1 0 * d' * x 0 0 + q * d' ^ 2 * x 1 0 - t 1 0 ^ 2 * x' - t 1 0 * d' * x 1 1)
      (by ring)

theorem conj_11_mod (ht : IsAL M q t) (x : SL(2, ℤ)) (hxM : (M : ℤ) ∣ x 1 0) :
    (((t * x * t⁻¹ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) = ((x 1 1 : ℤ) : ZMod M) := by
  rw [conj_11]
  push_cast
  rw [ht.c_zero, ht.d_one, ht.a_one, (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hxM]
  ring

theorem dvd_conj_inv_01 (ht : IsAL M q t) (y : SL(2, ℤ)) (hy : (q : ℤ) ∣ y 1 0) :
    (q : ℤ) ∣ (t⁻¹ * y * t : SL(2, ℤ)) 0 1 := by
  rw [conj_inv_01]
  obtain ⟨d', hd'⟩ := ht.d_dvd
  obtain ⟨y', hy'⟩ := hy
  rw [hd', hy']
  exact Dvd.intro ((d' * y 0 0 - t 0 1 * y') * t 0 1 + (q * d' * y 0 1 - t 0 1 * y 1 1) * d')
    (by ring)

theorem inv_not_mem_Gamma0 (ht : IsAL M q t) (hq : q.Prime) : t⁻¹ ∉ Gamma0 (M * q) := by
  intro h
  rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd, (inv_apply' t).2.2.1, dvd_neg] at h
  exact ht.not_dvd_c hq (dvd_trans (by push_cast; exact dvd_mul_left _ _) h)

theorem uinv_10 (j : ℤ) (g : SL(2, ℤ)) :
    (t * (uMat j)⁻¹ * g : SL(2, ℤ)) 1 0 = t 1 0 * (g 0 0 - j * g 1 0) + t 1 1 * g 1 0 := by
  rw [mul_apply', mul_apply', mul_apply', (inv_apply' (uMat j)).1, (inv_apply' (uMat j)).2.1,
    (inv_apply' (uMat j)).2.2.1, (inv_apply' (uMat j)).2.2.2]
  simp only [uMat_apply_00, uMat_apply_01, uMat_apply_10, uMat_apply_11]
  ring

theorem bruhat (ht : IsAL M q t) (hq : q.Prime) (hcop : IsCoprime (M : ℤ) (q : ℤ))
    (g : SL(2, ℤ)) (hg : (M : ℤ) ∣ g 1 0) :
    g ∈ Gamma0 (M * q) ∨ ∃ j : ℤ, t * (uMat j)⁻¹ * g ∈ Gamma0 (M * q) := by
  by_cases hc : (q : ℤ) ∣ g 1 0
  · left
    rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact mul_dvd_of_coprime hcop hg hc
  · right
    haveI : Fact q.Prime := ⟨hq⟩
    have hc0 : (((g 1 0 : ℤ)) : ZMod q) ≠ 0 := by
      rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    let j : ℤ := (((((g 0 0 : ℤ) : ZMod q) * (((g 1 0 : ℤ) : ZMod q))⁻¹).val : ℕ) : ℤ)
    refine ⟨j, ?_⟩
    rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd, uinv_10]
    have hj : (q : ℤ) ∣ g 0 0 - j * g 1 0 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      simp only [j, Int.cast_natCast, ZMod.natCast_zmod_val]
      rw [mul_assoc, ZMod.inv_mul_of_unit _ (IsUnit.mk0 (G₀ := ZMod q) _ hc0), mul_one, sub_self]
    have hM : (M : ℤ) ∣ t 1 1 * g 1 0 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_mul, ht.d_one,
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hg, mul_zero]
    apply mul_dvd_of_coprime hcop
    · exact dvd_add (dvd_mul_of_dvd_left ht.c_dvd _) hM
    · exact dvd_add (dvd_mul_of_dvd_right hj _) (dvd_mul_of_dvd_left ht.d_dvd _)

theorem mul_inv_mem_Gamma0 (ht : IsAL M q t) {t' : SL(2, ℤ)} (ht' : IsAL M q t')
    (hcop : IsCoprime (M : ℤ) (q : ℤ)) : t' * t⁻¹ ∈ Gamma0 (M * q) := by
  rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd, mul_apply', (inv_apply' t).1,
    (inv_apply' t).2.2.1]
  apply mul_dvd_of_coprime hcop
  · exact dvd_add (dvd_mul_of_dvd_left ht'.c_dvd _) (dvd_mul_of_dvd_right ht.c_dvd.neg_right _)
  · exact dvd_add (dvd_mul_of_dvd_right ht.d_dvd _) (dvd_mul_of_dvd_left ht'.d_dvd _)

def sMat (t : SL(2, ℤ)) (h : (q : ℤ) ∣ t 1 1) : SL(2, ℤ) :=
  ⟨!![q * t 0 0, t 0 1; t 1 0, t 1 1 / q], by
    rw [Matrix.det_fin_two_of]
    have h1 : (q : ℤ) * t 0 0 * (t 1 1 / q) = t 0 0 * t 1 1 := by
      rw [mul_comm (q : ℤ), mul_assoc, Int.mul_ediv_cancel' h]
    rw [h1]
    exact det_eq' t⟩

@[scoped simp] theorem sMat_00 (h : (q : ℤ) ∣ t 1 1) : (sMat t h) 0 0 = q * t 0 0 := rfl
@[scoped simp] theorem sMat_01 (h : (q : ℤ) ∣ t 1 1) : (sMat t h) 0 1 = t 0 1 := rfl
@[scoped simp] theorem sMat_10 (h : (q : ℤ) ∣ t 1 1) : (sMat t h) 1 0 = t 1 0 := rfl
@[scoped simp] theorem sMat_11 (h : (q : ℤ) ∣ t 1 1) : (sMat t h) 1 1 = t 1 1 / q := rfl

theorem sq_mem_Gamma0 (ht : IsAL M q t) (hcop : IsCoprime (M : ℤ) (q : ℤ)) :
    t * sMat t ht.d_dvd ∈ Gamma0 (M * q) := by
  rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd, mul_apply', sMat_00, sMat_10]
  apply mul_dvd_of_coprime hcop
  · exact dvd_add (dvd_mul_of_dvd_left ht.c_dvd _) (dvd_mul_of_dvd_right ht.c_dvd _)
  · have : t 1 0 * (q * t 0 0) + t 1 1 * t 1 0 = t 1 0 * (q * t 0 0 + t 1 1) := by ring
    rw [this]
    exact dvd_mul_of_dvd_right (dvd_add (dvd_mul_right _ _) ht.d_dvd) _

theorem sq_11_mul_q (ht : IsAL M q t) :
    (((t * sMat t ht.d_dvd : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) * (q : ZMod M) = 1 := by
  rw [mul_apply', sMat_01, sMat_11]
  have h : ((t 1 0 * t 0 1 + t 1 1 * (t 1 1 / q)) * q : ℤ) = t 1 0 * t 0 1 * q + t 1 1 * t 1 1 := by
    rw [add_mul, mul_assoc (t 1 1), Int.ediv_mul_cancel ht.d_dvd]
  have h2 : (((t 1 0 * t 0 1 + t 1 1 * (t 1 1 / q) : ℤ)) : ZMod M) * (q : ZMod M) =
      (((t 1 0 * t 0 1 + t 1 1 * (t 1 1 / q)) * q : ℤ) : ZMod M) := by
    push_cast; ring
  rw [h2, h]
  push_cast
  rw [ht.c_zero, ht.d_one]
  ring

theorem dMat_mul_dMat [NeZero q] (ht : IsAL M q t) :
    dMat q * toGLQ t * dMat q = zMat q * toGLQ (sMat t ht.d_dvd) := by
  have hq' : ((q : ℤ) : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have key : (q : ℚ) * (((t 1 1 / q : ℤ)) : ℚ) = ((t 1 1 : ℤ) : ℚ) := by
    rw [Int.cast_div ht.d_dvd hq', Int.cast_natCast]
    exact mul_div_cancel₀ _ hqQ
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [GL_mul_apply, key]
  all_goals ring

end IsAL
p2m_reactivate "P2MW.S_CohCarrier_exists_atkinLehnerOp_iDegL_jDegL_five_identities_of_prime.AtkinLehnerH1Sol.IsAL"

def tB (u v : ℤ) (huv : u * q + v * M = 1) : SL(2, ℤ) :=
  ⟨!![1, -v; (M : ℤ), u * q], by rw [Matrix.det_fin_two_of]; linear_combination huv⟩

theorem isAL_tB (u v : ℤ) (huv : u * q + v * M = 1) : IsAL M q (tB u v huv) := by
  refine ⟨?_, ?_, ?_⟩
  · show (M : ℤ) ∣ (M : ℤ); exact dvd_rfl
  · show (((u * q : ℤ)) : ZMod M) = 1
    have h : (u * q : ℤ) = 1 - v * M := by linear_combination huv
    rw [h]; push_cast; simp
  · show (q : ℤ) ∣ u * q; exact dvd_mul_left _ _

def tC (ℓ : ℕ) (u v : ℤ) (huv : u * q + v * (ℓ * M) = 1) : SL(2, ℤ) :=
  ⟨!![1, -v; (ℓ * M : ℤ), u * q], by rw [Matrix.det_fin_two_of]; linear_combination huv⟩

theorem isAL_tC (ℓ : ℕ) (u v : ℤ) (huv : u * q + v * (ℓ * M) = 1) : IsAL M q (tC ℓ u v huv) := by
  refine ⟨?_, ?_, ?_⟩
  · show (M : ℤ) ∣ (ℓ * M : ℤ); exact dvd_mul_left _ _
  · show (((u * q : ℤ)) : ZMod M) = 1
    have h : (u * q : ℤ) = 1 - v * ℓ * M := by linear_combination huv
    rw [h]; push_cast; simp
  · show (q : ℤ) ∣ u * q; exact dvd_mul_left _ _

theorem tB_huv (ℓ : ℕ) (u v : ℤ) (huv : u * q + v * (ℓ * M) = 1) : u * q + v * ℓ * M = 1 := by
  linear_combination huv

theorem aMat_mul_tB (ℓ : ℕ) [NeZero ℓ] (u v : ℤ) (huv : u * q + v * (ℓ * M) = 1) :
    aMat ℓ * toGLQ (tB (M := M) (q := q) u (v * ℓ) (tB_huv ℓ u v huv)) =
      toGLQ (tC (M := M) (q := q) ℓ u v huv) * aMat ℓ := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [GL_mul_apply, tB, tC]
  all_goals ring

theorem entry01_of_aMat_mul (ℓ : ℕ) [NeZero ℓ] {X Y : SL(2, ℤ)} (h : aMat ℓ * toGLQ X = toGLQ Y * aMat ℓ) :
    X 0 1 = Y 0 1 * ℓ := by
  have h' := congrArg (fun Z : GL (Fin 2) ℚ => (Z : Matrix (Fin 2) (Fin 2) ℚ) 0 1) h
  simp [GL_mul_apply] at h'
  exact_mod_cast h'

end Matrices
p2m_reactivate "P2MW.S_CohCarrier_exists_atkinLehnerOp_iDegL_jDegL_five_identities_of_prime.AtkinLehnerH1Sol.IsAL"

section Level

open CohCarrier CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups

variable {M q : ℕ} [NeZero M] [NeZero q] [NeZero (M * q)]
variable {H : Subgroup (ZMod M)ˣ} {H' : Subgroup (ZMod (M * q))ˣ}

theorem levelLE_q (hH' : ∀ v : (ZMod (M * q))ˣ, v ∈ H' ↔ ZMod.unitsMap (dvd_mul_right M q) v ∈ H) :
    LevelLE M (M * q) H H' q :=
  ⟨dvd_mul_right M q, by rw [Nat.mul_div_cancel_left q (Nat.pos_of_ne_zero (NeZero.ne M))],
    fun v hv => (hH' v).mp hv⟩

theorem mem_Gamma0_of_mul {x : SL(2, ℤ)} (hx : x ∈ Gamma0 (M * q)) : x ∈ Gamma0 M := by
  rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hx ⊢
  exact dvd_trans (by push_cast; exact dvd_mul_right _ _) hx

theorem unitsMap_gamma0Units (x : Gamma0 (M * q)) :
    ZMod.unitsMap (dvd_mul_right M q) (gamma0Units (M * q) x) =
      gamma0Units M ⟨(x : SL(2, ℤ)), mem_Gamma0_of_mul x.2⟩ := by
  apply Units.ext
  simp [ZMod.unitsMap, gamma0Units, Gamma0Map]

theorem val_unitsMap_gamma0Units (x : Gamma0 (M * q)) :
    ((ZMod.unitsMap (dvd_mul_right M q) (gamma0Units (M * q) x) : (ZMod M)ˣ) : ZMod M) =
      (((x : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) := by
  rw [unitsMap_gamma0Units]
  simp [gamma0Units, Gamma0Map]

section Ranges

variable (hH' : ∀ v : (ZMod (M * q))ˣ, v ∈ H' ↔ ZMod.unitsMap (dvd_mul_right M q) v ∈ H)
variable (h1 : LevelLE M (M * q) H H' 1)

include hH'

theorem mem_GammaH_mul_of_mem (x : ↥(GammaH M H)) (hx : (x : SL(2, ℤ)) ∈ Gamma0 (M * q)) :
    (x : SL(2, ℤ)) ∈ GammaH (M * q) H' := by
  obtain ⟨hx0, hxH⟩ := mem_GammaH_iff.mp x.2
  refine mem_GammaH_iff.mpr ⟨hx, (hH' _).mpr ?_⟩
  rw [unitsMap_gamma0Units]
  exact hxH

theorem mem_range_one_iff (x : ↥(GammaH M H)) :
    x ∈ (iotaDeg M (M * q) H H' 1 h1).range ↔ (x : SL(2, ℤ)) ∈ Gamma0 (M * q) := by
  constructor
  · rintro ⟨γ, rfl⟩
    rw [coe_iotaDeg_one h1]
    exact (mem_GammaH_iff.mp γ.2).1
  · intro hx
    exact ⟨⟨(x : SL(2, ℤ)), mem_GammaH_mul_of_mem hH' x hx⟩, Subtype.ext (coe_iotaDeg_one h1 _)⟩

theorem mem_range_q_iff (hq' : LevelLE M (M * q) H H' q) (x : ↥(GammaH M H)) :
    x ∈ (iotaDeg M (M * q) H H' q hq').range ↔ (q : ℤ) ∣ (x : SL(2, ℤ)) 0 1 := by
  constructor
  · rintro ⟨g, rfl⟩
    show (q : ℤ) ∣ (conjLowerMat q (g : SL(2, ℤ)) (hq'.dvd_entry g)) 0 1
    simp [conjLowerMat]
  · intro hdiv
    obtain ⟨hx0, hxH⟩ := mem_GammaH_iff.mp x.2
    have hxM : (M : ℤ) ∣ (x : SL(2, ℤ)) 1 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hx0)
    have h0 : conjUpperMat q (x : SL(2, ℤ)) hdiv ∈ Gamma0 (M * q) := by
      rw [Gamma0_mem, conjUpperMat_apply_10, ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      exact mul_dvd_mul hxM (dvd_refl _)
    have hmem : conjUpperMat q (x : SL(2, ℤ)) hdiv ∈ GammaH (M * q) H' := by
      refine mem_GammaH_iff.mpr ⟨h0, (hH' _).mpr ?_⟩
      rw [unitsMap_gamma0Units]
      have he : gamma0Units M ⟨conjUpperMat q (x : SL(2, ℤ)) hdiv, mem_Gamma0_of_mul h0⟩ =
          gamma0Units M ⟨(x : SL(2, ℤ)), hx0⟩ :=
        Units.ext (by simp [gamma0Units, Gamma0Map])
      rw [he]
      exact hxH
    refine ⟨⟨conjUpperMat q (x : SL(2, ℤ)) hdiv, hmem⟩, Subtype.ext ?_⟩
    exact conjLowerMat_conjUpperMat q (x : SL(2, ℤ)) hdiv
      (hq'.dvd_entry ⟨conjUpperMat q (x : SL(2, ℤ)) hdiv, hmem⟩)

end Ranges
p2m_reactivate "P2MW.S_CohCarrier_exists_atkinLehnerOp_iDegL_jDegL_five_identities_of_prime.AtkinLehnerH1Sol.IsAL"

theorem iota_q_conjL (h1 : LevelLE M (M * q) H H' 1) (hq' : LevelLE M (M * q) H H' q) (k : ↥(GammaHUpper (M * q) H' q)) :
    iotaDeg M (M * q) H H' q hq' (conjL (M * q) H' q k) = iotaDeg M (M * q) H H' 1 h1 k := by
  apply Subtype.ext
  rw [coe_iotaDeg_one h1]
  exact conjLowerMat_conjUpperMat q ((k : ↥(GammaH (M * q) H')) : SL(2, ℤ))
    (dvd_of_mem_GammaHUpper (M * q) H' q k) (hq'.dvd_entry (conjL (M * q) H' q k))

theorem apply_conj {N : ℕ} {K : Subgroup (ZMod N)ˣ} {A : Type*} [AddCommGroup A]
    (ψ : H1 N K A) (r x : ↥(GammaH N K)) :
    ψ (Additive.ofMul (r * x * r⁻¹)) = ψ (Additive.ofMul x) := by
  rw [ofMul_mul, ofMul_mul, ofMul_inv, map_add, map_add, map_neg]
  abel

section AL

def tW {t : SL(2, ℤ)} (H : Subgroup (ZMod M)ˣ) (ht : IsAL M q t) : ↥(GammaH M H) :=
  ⟨t, ht.mem_GammaH H⟩

@[scoped simp] theorem coe_tW {t : SL(2, ℤ)} (ht : IsAL M q t) :
    ((tW H ht : ↥(GammaH M H)) : SL(2, ℤ)) = t := rfl

noncomputable def EM (q : ℕ) [NeZero q] (t : SL(2, ℤ)) : GL (Fin 2) ℚ := toGLQ t * dMat q

section SigmaFacts

variable (σ : Gamma0 (M * q))

theorem q_dvd_sigma : (q : ℤ) ∣ (σ : SL(2, ℤ)) 1 0 :=
  dvd_trans (by push_cast; exact dvd_mul_left _ _)
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp σ.2))

theorem M_dvd_conjLowerMat_sigma : (M : ℤ) ∣ (conjLowerMat q (σ : SL(2, ℤ)) (q_dvd_sigma σ)) 1 0 := by
  show (M : ℤ) ∣ (σ : SL(2, ℤ)) 1 0 / q
  obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp σ.2)
  rw [hk, show ((M * q : ℕ) : ℤ) * k = (q : ℤ) * (M * k) by push_cast; ring,
    Int.mul_ediv_cancel_left _ (by exact_mod_cast NeZero.ne q)]
  exact dvd_mul_right _ _

end SigmaFacts
p2m_reactivate "P2MW.S_CohCarrier_exists_atkinLehnerOp_iDegL_jDegL_five_identities_of_prime.AtkinLehnerH1Sol.IsAL"

theorem mem_upper_iff_dvd (k : ↥(GammaH (M * q) H')) :
    k ∈ GammaHUpper (M * q) H' q ↔ (q : ℤ) ∣ (k : SL(2, ℤ)) 0 1 := by
  rw [Subgroup.mem_subgroupOf, mem_Gamma0Upper, ZMod.intCast_zmod_eq_zero_iff_dvd]

theorem M_dvd_10 (k : ↥(GammaH (M * q) H')) : (M : ℤ) ∣ (k : SL(2, ℤ)) 1 0 :=
  dvd_trans (by push_cast; exact dvd_mul_right _ _)
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp (mem_GammaH_iff.mp k.2).1))

variable (hH' : ∀ v : (ZMod (M * q))ˣ, v ∈ H' ↔ ZMod.unitsMap (dvd_mul_right M q) v ∈ H)
variable (h1 : LevelLE M (M * q) H H' 1)
variable (hcop : IsCoprime (M : ℤ) (q : ℤ))
variable {t : SL(2, ℤ)} (ht : IsAL M q t)

include hH' h1 hcop ht

theorem conj_iota_q_mem (γ : ↥(GammaH (M * q) H')) :
    tW H ht * iotaDeg M (M * q) H H' q (levelLE_q hH') γ * (tW H ht)⁻¹ ∈
      (iotaDeg M (M * q) H H' 1 h1).range := by
  rw [mem_range_one_iff hH' h1]
  show t * conjLowerMat q (γ : SL(2, ℤ)) ((levelLE_q hH').dvd_entry γ) * t⁻¹ ∈ Gamma0 (M * q)
  refine ht.conj_mem_Gamma0 hcop _ ?_ ?_
  · exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp
      (GammaH_le_Gamma0 H (iotaDeg M (M * q) H H' q (levelLE_q hH') γ).2))
  · show (q : ℤ) ∣ (conjLowerMat q (γ : SL(2, ℤ)) ((levelLE_q hH').dvd_entry γ)) 0 1
    simp [conjLowerMat]

noncomputable def alHom : ↥(GammaH (M * q) H') →* ↥(GammaH (M * q) H') :=
  (MonoidHom.ofInjective (iotaDeg_injective M (M * q) H H' 1 h1)).symm.toMonoidHom.comp
    ((((MulAut.conj (tW H ht)).toMonoidHom.comp (iotaDeg M (M * q) H H' q (levelLE_q hH'))).codRestrict
      (iotaDeg M (M * q) H H' 1 h1).range (conj_iota_q_mem hH' h1 hcop ht)))

theorem iota_alHom (γ : ↥(GammaH (M * q) H')) :
    iotaDeg M (M * q) H H' 1 h1 (alHom hH' h1 hcop ht γ) =
      tW H ht * iotaDeg M (M * q) H H' q (levelLE_q hH') γ * (tW H ht)⁻¹ := by
  show iotaDeg M (M * q) H H' 1 h1
    ((MonoidHom.ofInjective (iotaDeg_injective M (M * q) H H' 1 h1)).symm ⟨_, _⟩) = _
  rw [MonoidHom.apply_ofInjective_symm]
  rfl

theorem coe_alHom (γ : ↥(GammaH (M * q) H')) :
    ((alHom hH' h1 hcop ht γ : ↥(GammaH (M * q) H')) : SL(2, ℤ)) =
      t * conjLowerMat q (γ : SL(2, ℤ)) ((levelLE_q hH').dvd_entry γ) * t⁻¹ := by
  rw [← coe_iotaDeg_one h1 (alHom hH' h1 hcop ht γ), iota_alHom]
  rfl

theorem toGLQ_alHom (γ : ↥(GammaH (M * q) H')) :
    toGLQ ((alHom hH' h1 hcop ht γ : ↥(GammaH (M * q) H')) : SL(2, ℤ)) =
      EM q t * toGLQ (γ : SL(2, ℤ)) * (EM q t)⁻¹ := by
  rw [coe_alHom, map_mul, map_mul, map_inv, toGLQ_conjLowerMat]
  simp only [EM, mul_inv_rev, mul_assoc]

theorem alHom_injective : Function.Injective (alHom hH' h1 hcop ht) := by
  intro a b h
  have h' := congrArg (iotaDeg M (M * q) H H' 1 h1) h
  rw [iota_alHom, iota_alHom] at h'
  simp only [mul_left_inj, mul_right_inj] at h'
  exact iotaDeg_injective M (M * q) H H' q (levelLE_q hH') h'

theorem alHom_surjective : Function.Surjective (alHom hH' h1 hcop ht) := by
  intro γ
  have hy : (tW H ht)⁻¹ * iotaDeg M (M * q) H H' 1 h1 γ * tW H ht ∈
      (iotaDeg M (M * q) H H' q (levelLE_q hH')).range := by
    rw [mem_range_q_iff hH']
    have hc : ((tW H ht)⁻¹ * iotaDeg M (M * q) H H' 1 h1 γ * tW H ht : ↥(GammaH M H)) =
        (t⁻¹ * (γ : SL(2, ℤ)) * t : SL(2, ℤ)) := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, InvMemClass.coe_inv, coe_iotaDeg_one h1]; rfl
    rw [hc]
    refine ht.dvd_conj_inv_01 _ (dvd_trans ?_ ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      (Gamma0_mem.mp (mem_GammaH_iff.mp γ.2).1)))
    push_cast
    exact dvd_mul_left _ _
  obtain ⟨γ', hγ'⟩ := hy
  refine ⟨γ', iotaDeg_injective M (M * q) H H' 1 h1 ?_⟩
  rw [iota_alHom, hγ']
  group

noncomputable def alEquiv : ↥(GammaH (M * q) H') ≃* ↥(GammaH (M * q) H') :=
  MulEquiv.ofBijective (alHom hH' h1 hcop ht) ⟨alHom_injective hH' h1 hcop ht,
    alHom_surjective hH' h1 hcop ht⟩

@[scoped simp] theorem alEquiv_apply (γ : ↥(GammaH (M * q) H')) :
    alEquiv hH' h1 hcop ht γ = alHom hH' h1 hcop ht γ := rfl

variable (𝒪 : Type) [CommRing 𝒪]

noncomputable def wOp : Module.End 𝒪 (H1 (M * q) H' 𝒪) where
  toFun ψ := ψ.comp (MonoidHom.toAdditive (alHom hH' h1 hcop ht))
  map_add' := by intro φ ψ; ext; rfl
  map_smul' := by intro r φ; ext; rfl

theorem wOp_iDeg (φ : H1 M H 𝒪) :
    wOp hH' h1 hcop ht 𝒪 (iDeg' M (M * q) H H' 1 𝒪 h1 φ) =
      iDeg' M (M * q) H H' q 𝒪 (levelLE_q hH') φ := by
  refine AddMonoidHom.ext fun a => ?_
  show φ (Additive.ofMul (iotaDeg M (M * q) H H' 1 h1 (alHom hH' h1 hcop ht (Additive.toMul a)))) =
    φ (Additive.ofMul (iotaDeg M (M * q) H H' q (levelLE_q hH') (Additive.toMul a)))
  rw [iota_alHom, apply_conj]

theorem alHom_eq_conj {t' : SL(2, ℤ)} (ht' : IsAL M q t') (γ : ↥(GammaH (M * q) H')) :
    ∃ r : ↥(GammaH (M * q) H'),
      alHom hH' h1 hcop ht' γ = r * alHom hH' h1 hcop ht γ * r⁻¹ := by
  have hr : tW H ht' * (tW H ht)⁻¹ ∈ (iotaDeg M (M * q) H H' 1 h1).range := by
    rw [mem_range_one_iff hH' h1]
    exact ht.mul_inv_mem_Gamma0 ht' hcop
  refine ⟨(MonoidHom.ofInjective (iotaDeg_injective M (M * q) H H' 1 h1)).symm ⟨_, hr⟩,
    iotaDeg_injective M (M * q) H H' 1 h1 ?_⟩
  rw [map_mul, map_mul, map_inv, iota_alHom, iota_alHom, MonoidHom.apply_ofInjective_symm]
  group

theorem wOp_eq_of_isAL {t' : SL(2, ℤ)} (ht' : IsAL M q t') :
    wOp hH' h1 hcop ht 𝒪 = wOp hH' h1 hcop ht' 𝒪 := by
  refine LinearMap.ext fun ψ => AddMonoidHom.ext fun a => ?_
  obtain ⟨r, hr⟩ := alHom_eq_conj hH' h1 hcop ht ht' (Additive.toMul a)
  show ψ (Additive.ofMul (alHom hH' h1 hcop ht (Additive.toMul a))) =
    ψ (Additive.ofMul (alHom hH' h1 hcop ht' (Additive.toMul a)))
  rw [hr, apply_conj]

def gamma0Sq : Gamma0 (M * q) := ⟨t * IsAL.sMat t ht.d_dvd, ht.sq_mem_Gamma0 hcop⟩

theorem EM_mul_EM : EM q t * EM q t = zMat q * toGLQ (t * IsAL.sMat t ht.d_dvd) := by
  simp only [EM]
  rw [map_mul]
  calc toGLQ t * dMat q * (toGLQ t * dMat q) = toGLQ t * (dMat q * toGLQ t * dMat q) := by group
    _ = toGLQ t * (zMat q * toGLQ (IsAL.sMat t ht.d_dvd)) := by rw [ht.dMat_mul_dMat]
    _ = zMat q * (toGLQ t * toGLQ (IsAL.sMat t ht.d_dvd)) := by
        rw [← mul_assoc, ← zMat_comm, mul_assoc]

theorem alHom_alHom (γ : ↥(GammaH (M * q) H')) :
    alHom hH' h1 hcop ht (alHom hH' h1 hcop ht γ) =
      conjHom (M * q) H' (gamma0Sq hcop ht) γ := by
  apply Subtype.ext
  apply toGLQ_injective
  rw [toGLQ_alHom, toGLQ_alHom]
  show _ = toGLQ ((t * IsAL.sMat t ht.d_dvd) * (γ : SL(2, ℤ)) * (t * IsAL.sMat t ht.d_dvd)⁻¹)
  rw [map_mul, map_mul, map_inv]
  set Y := toGLQ (t * IsAL.sMat t ht.d_dvd)
  set G := toGLQ (γ : SL(2, ℤ))
  have hE := EM_mul_EM hH' h1 hcop ht
  rw [show EM q t * (EM q t * G * (EM q t)⁻¹) * (EM q t)⁻¹ =
      (EM q t * EM q t) * G * (EM q t * EM q t)⁻¹ by group, hE, mul_inv_rev,
    show zMat q * Y * G * (Y⁻¹ * (zMat q)⁻¹) = (zMat q * (Y * G * Y⁻¹)) * (zMat q)⁻¹ by group,
    zMat_comm, mul_inv_cancel_right]

theorem wOp_wOp (ψ : H1 (M * q) H' 𝒪) :
    wOp hH' h1 hcop ht 𝒪 (wOp hH' h1 hcop ht 𝒪 ψ) = diamondRaw (M * q) H' 𝒪 (gamma0Sq hcop ht) ψ := by
  refine AddMonoidHom.ext fun a => ?_
  show ψ (Additive.ofMul (alHom hH' h1 hcop ht (alHom hH' h1 hcop ht (Additive.toMul a)))) =
    ψ (Additive.ofMul (conjHom (M * q) H' (gamma0Sq hcop ht) (Additive.toMul a)))
  rw [alHom_alHom]

theorem unitsMap_gamma0Sq_mul_q :
    ((ZMod.unitsMap (dvd_mul_right M q) (gamma0Units (M * q) (gamma0Sq hcop ht)) : (ZMod M)ˣ) :
        ZMod M) * (q : ZMod M) = 1 := by
  rw [val_unitsMap_gamma0Units]
  exact ht.sq_11_mul_q

section Diamond

variable (σ : Gamma0 (M * q))

theorem ySigma_mem : t * conjLowerMat q (σ : SL(2, ℤ)) (q_dvd_sigma σ) * t⁻¹ ∈ Gamma0 (M * q) :=
  ht.conj_mem_Gamma0 hcop _ (M_dvd_conjLowerMat_sigma σ)
    (by show (q : ℤ) ∣ (σ : SL(2, ℤ)) 0 1 * q; exact dvd_mul_left _ _)

def rhoSigma : Gamma0 (M * q) := ⟨_, ySigma_mem hH' h1 hcop ht σ⟩ * σ⁻¹

theorem rhoSigma_mem : ((rhoSigma hH' h1 hcop ht σ : Gamma0 (M * q)) : SL(2, ℤ)) ∈ GammaH (M * q) H' := by
  refine mem_GammaH_iff.mpr ⟨(rhoSigma hH' h1 hcop ht σ).2, (hH' _).mpr ?_⟩
  rw [Subtype.coe_eta, rhoSigma, map_mul, map_inv, map_mul, map_inv]
  have he : ZMod.unitsMap (dvd_mul_right M q) (gamma0Units (M * q) ⟨_, ySigma_mem hH' h1 hcop ht σ⟩) =
      ZMod.unitsMap (dvd_mul_right M q) (gamma0Units (M * q) σ) := by
    apply Units.ext
    rw [val_unitsMap_gamma0Units, val_unitsMap_gamma0Units]
    rw [ht.conj_11_mod _ (M_dvd_conjLowerMat_sigma σ)]
    simp [conjLowerMat]
  rw [he, mul_inv_cancel]
  exact H.one_mem

theorem toGLQ_rhoSigma :
    toGLQ ((rhoSigma hH' h1 hcop ht σ : Gamma0 (M * q)) : SL(2, ℤ)) =
      EM q t * toGLQ (σ : SL(2, ℤ)) * (EM q t)⁻¹ * (toGLQ (σ : SL(2, ℤ)))⁻¹ := by
  show toGLQ (t * conjLowerMat q (σ : SL(2, ℤ)) (q_dvd_sigma σ) * t⁻¹ * (σ : SL(2, ℤ))⁻¹) = _
  rw [map_mul, map_inv, map_mul, map_mul, map_inv, toGLQ_conjLowerMat]
  simp only [EM, mul_inv_rev, mul_assoc]

def rhoElt : ↥(GammaH (M * q) H') := ⟨_, rhoSigma_mem hH' h1 hcop ht σ⟩

theorem alHom_conjHom (γ : ↥(GammaH (M * q) H')) :
    alHom hH' h1 hcop ht (conjHom (M * q) H' σ γ) =
      rhoElt hH' h1 hcop ht σ * conjHom (M * q) H' σ (alHom hH' h1 hcop ht γ) * (rhoElt hH' h1 hcop ht σ)⁻¹ := by
  apply Subtype.ext
  apply toGLQ_injective
  rw [toGLQ_alHom]
  show EM q t * toGLQ ((σ : SL(2, ℤ)) * (γ : SL(2, ℤ)) * (σ : SL(2, ℤ))⁻¹) * (EM q t)⁻¹ =
    toGLQ (((rhoSigma hH' h1 hcop ht σ : Gamma0 (M * q)) : SL(2, ℤ)) *
      ((σ : SL(2, ℤ)) * ((alHom hH' h1 hcop ht γ : ↥(GammaH (M * q) H')) : SL(2, ℤ)) * (σ : SL(2, ℤ))⁻¹) *
      ((rhoSigma hH' h1 hcop ht σ : Gamma0 (M * q)) : SL(2, ℤ))⁻¹)
  simp only [map_mul, map_inv, toGLQ_rhoSigma, toGLQ_alHom]
  group

theorem wOp_diamondRaw (ψ : H1 (M * q) H' 𝒪) :
    wOp hH' h1 hcop ht 𝒪 (diamondRaw (M * q) H' 𝒪 σ ψ) =
      diamondRaw (M * q) H' 𝒪 σ (wOp hH' h1 hcop ht 𝒪 ψ) := by
  refine AddMonoidHom.ext fun a => ?_
  show ψ (Additive.ofMul (conjHom (M * q) H' σ (alHom hH' h1 hcop ht (Additive.toMul a)))) =
    ψ (Additive.ofMul (alHom hH' h1 hcop ht (conjHom (M * q) H' σ (Additive.toMul a))))
  rw [alHom_conjHom, apply_conj]

end Diamond
p2m_reactivate "P2MW.S_CohCarrier_exists_atkinLehnerOp_iDegL_jDegL_five_identities_of_prime.AtkinLehnerH1Sol.IsAL"

section Trace

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

def Kt : Subgroup ↥((iotaDeg M (M * q) H H' 1 h1).range) :=
  ((iotaDeg M (M * q) H H' 1 h1).range).comap
    ((MulAut.conj (tW H ht)).toMonoidHom.comp ((iotaDeg M (M * q) H H' 1 h1).range.subtype))

theorem mem_Kt (l : ↥((iotaDeg M (M * q) H H' 1 h1).range)) :
    l ∈ Kt h1 ht ↔
      tW H ht * (l : ↥(GammaH M H)) * (tW H ht)⁻¹ ∈ (iotaDeg M (M * q) H H' 1 h1).range :=
  Iff.rfl

theorem mem_Kt' (l : ↥((iotaDeg M (M * q) H H' 1 h1).range)) :
    l ∈ Kt h1 ht ↔
      ((tW H ht)⁻¹)⁻¹ * (l : ↥(GammaH M H)) * (tW H ht)⁻¹ ∈ (iotaDeg M (M * q) H H' 1 h1).range := by
  rw [inv_inv]; rfl

theorem mem_upper_iff_Kt (k : ↥(GammaH (M * q) H')) :
    k ∈ GammaHUpper (M * q) H' q ↔
      MonoidHom.ofInjective (iotaDeg_injective M (M * q) H H' 1 h1) k ∈ Kt h1 ht := by
  rw [mem_Kt hH' h1 hcop ht, mem_upper_iff_dvd]
  have hc : ((tW H ht * ((MonoidHom.ofInjective (iotaDeg_injective M (M * q) H H' 1 h1) k :
      ↥((iotaDeg M (M * q) H H' 1 h1).range)) : ↥(GammaH M H)) * (tW H ht)⁻¹ : ↥(GammaH M H)) :
        SL(2, ℤ)) = t * (k : SL(2, ℤ)) * t⁻¹ := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, InvMemClass.coe_inv, MonoidHom.ofInjective_apply,
      coe_iotaDeg_one h1]; rfl
  rw [mem_range_one_iff hH' h1, hc]
  constructor
  · intro hk
    exact ht.conj_mem_Gamma0 hcop _ (M_dvd_10 k) hk
  · intro hy
    have h2 := ht.dvd_conj_inv_01 _ (dvd_trans (by push_cast; exact dvd_mul_left _ _)
      ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hy)))
    rwa [show t⁻¹ * (t * (k : SL(2, ℤ)) * t⁻¹) * t = (k : SL(2, ℤ)) by group] at h2

theorem Kt_finiteIndex : (Kt h1 ht).FiniteIndex := by
  refine ⟨?_⟩
  rw [Subgroup.index_eq_card, ← Nat.card_congr (quotEquiv
    (MonoidHom.ofInjective (iotaDeg_injective M (M * q) H H' 1 h1)) (GammaHUpper (M * q) H' q)
    (Kt h1 ht) (mem_upper_iff_Kt hH' h1 hcop ht)), ← Subgroup.index_eq_card]
  exact Subgroup.FiniteIndex.index_ne_zero

theorem bruhat_range (hq : q.Prime) (g : ↥(GammaH M H)) :
    g ∈ (iotaDeg M (M * q) H H' 1 h1).range ∨
      ∃ l ∈ (iotaDeg M (M * q) H H' 1 h1).range,
        ((tW H ht)⁻¹)⁻¹ * (l⁻¹ * g) ∈ (iotaDeg M (M * q) H H' 1 h1).range := by
  have hgM : (M : ℤ) ∣ (g : SL(2, ℤ)) 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp (mem_GammaH_iff.mp g.2).1)
  rcases ht.bruhat hq hcop (g : SL(2, ℤ)) hgM with hg | ⟨j, hj⟩
  · exact Or.inl ((mem_range_one_iff hH' h1 g).mpr hg)
  · refine Or.inr ⟨uElt M H j, (mem_range_one_iff hH' h1 _).mpr ?_, (mem_range_one_iff hH' h1 _).mpr ?_⟩
    · rw [coe_uElt, Gamma0_mem, uMat_apply_10, Int.cast_zero]
    · rw [inv_inv]
      show t * ((uMat j)⁻¹ * (g : SL(2, ℤ))) ∈ Gamma0 (M * q)
      rwa [← mul_assoc]

theorem tW_inv_not_mem (hq : q.Prime) : (tW H ht)⁻¹ ∉ (iotaDeg M (M * q) H H' 1 h1).range :=
  fun h => ht.inv_not_mem_Gamma0 hq ((mem_range_one_iff hH' h1 _).mp h)

theorem alHom_conjL (k : ↥(GammaHUpper (M * q) H' q))
    (x : ↥((iotaDeg M (M * q) H H' 1 h1).range))
    (hx : (x : ↥(GammaH M H)) = tW H ht * iotaDeg M (M * q) H H' 1 h1 k * (tW H ht)⁻¹) :
    alHom hH' h1 hcop ht (conjL (M * q) H' q k) =
      (MonoidHom.ofInjective (iotaDeg_injective M (M * q) H H' 1 h1)).symm x := by
  apply iotaDeg_injective M (M * q) H H' 1 h1
  rw [iota_alHom, iota_q_conjL h1, MonoidHom.apply_ofInjective_symm, hx]

theorem char_eq (ψ : H1 (M * q) H' 𝒪) :
    (AddMonoidHom.toMultiplicativeRight (wOp hH' h1 hcop ht 𝒪 ψ)).comp (conjL (M * q) H' q) =
      (conjChar _ ((tW H ht)⁻¹) (Kt h1 ht) (mem_Kt' hH' h1 hcop ht)
        (AddMonoidHom.toMultiplicativeRight (pushChar M (M * q) H H' 1 𝒪 h1 ψ))).comp
        (restrictEquiv (MonoidHom.ofInjective (iotaDeg_injective M (M * q) H H' 1 h1))
          (GammaHUpper (M * q) H' q) (Kt h1 ht) (mem_upper_iff_Kt hH' h1 hcop ht)) := by
  ext k
  simp only [MonoidHom.comp_apply, AddMonoidHom.toMultiplicativeRight_apply_apply, conjChar_apply]
  apply congrArg Multiplicative.ofAdd
  show ψ (Additive.ofMul (alHom hH' h1 hcop ht (conjL (M * q) H' q k))) =
    ψ (Additive.ofMul ((MonoidHom.ofInjective (iotaDeg_injective M (M * q) H H' 1 h1)).symm _))
  rw [alHom_conjL hH' h1 hcop ht k _ ?_]
  simp only [inv_inv, coe_restrictEquiv, MonoidHom.ofInjective_apply]
  rfl

theorem iDeg_jDeg (hq : q.Prime) (ψ : H1 (M * q) H' 𝒪) :
    iDeg' M (M * q) H H' 1 𝒪 h1 (jDeg M (M * q) H H' 1 𝒪 h1 ψ) =
      ψ + heckeT (M * q) H' q 𝒪 (wOp hH' h1 hcop ht 𝒪 ψ) := by
  haveI := Kt_finiteIndex hH' h1 hcop ht
  refine AddMonoidHom.ext fun a => ?_
  show Multiplicative.toAdd (MonoidHom.transfer
      (AddMonoidHom.toMultiplicativeRight (pushChar M (M * q) H H' 1 𝒪 h1 ψ))
      ((iotaDeg M (M * q) H H' 1 h1 (Additive.toMul a) : ↥(GammaH M H)))) =
    ψ a + Multiplicative.toAdd (MonoidHom.transfer
      ((AddMonoidHom.toMultiplicativeRight (wOp hH' h1 hcop ht 𝒪 ψ)).comp (conjL (M * q) H' q))
      (Additive.toMul a))
  have e1 : (iotaDeg M (M * q) H H' 1 h1 (Additive.toMul a) : ↥(GammaH M H)) =
      ((MonoidHom.ofInjective (iotaDeg_injective M (M * q) H H' 1 h1) (Additive.toMul a) :
        ↥((iotaDeg M (M * q) H H' 1 h1).range)) : ↥(GammaH M H)) := rfl
  rw [e1, transfer_mackey_self _ ((tW H ht)⁻¹) (Kt h1 ht) (mem_Kt' hH' h1 hcop ht)
    (bruhat_range hH' h1 hcop ht hq) (tW_inv_not_mem hH' h1 hcop ht hq), toAdd_mul, char_eq,
    transfer_comp_equiv]
  congr 1
  show ψ (Additive.ofMul ((MonoidHom.ofInjective (iotaDeg_injective M (M * q) H H' 1 h1)).symm
    (MonoidHom.ofInjective (iotaDeg_injective M (M * q) H H' 1 h1) (Additive.toMul a)))) = ψ a
  rw [MulEquiv.symm_apply_apply]
  rfl

end Trace
p2m_reactivate "P2MW.S_CohCarrier_exists_atkinLehnerOp_iDegL_jDegL_five_identities_of_prime.AtkinLehnerH1Sol.IsAL"

section HeckeComm

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

variable (ℓ : ℕ) [NeZero ℓ] {t' : SL(2, ℤ)} (ht' : IsAL M q t')
  (hℓt : toGLQ t' * aMat ℓ = aMat ℓ * toGLQ t)

include ht' hℓt

theorem EM_conj : EM q t' = aMat ℓ * EM q t * (aMat ℓ)⁻¹ := by
  have h : toGLQ t' = aMat ℓ * toGLQ t * (aMat ℓ)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq]; exact hℓt
  have comm' : (aMat ℓ)⁻¹ * dMat q = dMat q * (aMat ℓ)⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, aMat_dMat_comm, mul_assoc, mul_inv_cancel, mul_one]
  simp only [EM]
  rw [h]
  simp only [mul_assoc, comm']

theorem aMat_mul_alHom (k : ↥(GammaHUpper (M * q) H' ℓ)) :
    aMat ℓ * toGLQ ((alHom hH' h1 hcop ht (k : ↥(GammaH (M * q) H')) : ↥(GammaH (M * q) H')) : SL(2, ℤ)) =
      toGLQ ((alHom hH' h1 hcop ht' (conjL (M * q) H' ℓ k) : ↥(GammaH (M * q) H')) : SL(2, ℤ)) *
        aMat ℓ := by
  rw [toGLQ_alHom, toGLQ_alHom, EM_conj hH' h1 hcop ht ℓ ht' hℓt,
    show ((conjL (M * q) H' ℓ k : ↥(GammaH (M * q) H')) : SL(2, ℤ)) =
      conjUpperMat ℓ ((k : ↥(GammaH (M * q) H')) : SL(2, ℤ)) (dvd_of_mem_GammaHUpper _ _ _ k) from rfl,
    toGLQ_conjUpperMat]
  group

theorem alHom_mem_upper (k : ↥(GammaHUpper (M * q) H' ℓ)) :
    alHom hH' h1 hcop ht (k : ↥(GammaH (M * q) H')) ∈ GammaHUpper (M * q) H' ℓ := by
  rw [Subgroup.mem_subgroupOf, mem_Gamma0Upper, ZMod.intCast_zmod_eq_zero_iff_dvd,
    entry01_of_aMat_mul ℓ (aMat_mul_alHom hH' h1 hcop ht ℓ ht' hℓt k)]
  exact dvd_mul_left _ _

theorem conjL_alHom (k : ↥(GammaHUpper (M * q) H' ℓ))
    (hm : alHom hH' h1 hcop ht (k : ↥(GammaH (M * q) H')) ∈ GammaHUpper (M * q) H' ℓ) :
    conjL (M * q) H' ℓ ⟨alHom hH' h1 hcop ht (k : ↥(GammaH (M * q) H')), hm⟩ =
      alHom hH' h1 hcop ht' (conjL (M * q) H' ℓ k) := by
  apply Subtype.ext
  apply toGLQ_injective
  show toGLQ (conjUpperMat ℓ ((alHom hH' h1 hcop ht (k : ↥(GammaH (M * q) H')) :
      ↥(GammaH (M * q) H')) : SL(2, ℤ)) (dvd_of_mem_GammaHUpper _ _ _ ⟨_, hm⟩)) = _
  rw [toGLQ_conjUpperMat, aMat_mul_alHom hH' h1 hcop ht ℓ ht' hℓt k, mul_inv_cancel_right]

theorem wOp_heckeT (ψ : H1 (M * q) H' 𝒪) :
    wOp hH' h1 hcop ht 𝒪 (heckeT (M * q) H' ℓ 𝒪 ψ) = heckeT (M * q) H' ℓ 𝒪 (wOp hH' h1 hcop ht 𝒪 ψ) := by
  set e := alEquiv hH' h1 hcop ht
  have hHℓ : ∀ x, x ∈ GammaHUpper (M * q) H' ℓ ↔ e x ∈ GammaHUpper (M * q) H' ℓ :=
    mem_iff_of_forall_mem e _ (fun k hk => alHom_mem_upper hH' h1 hcop ht ℓ ht' hℓt ⟨k, hk⟩)
  set χ₂ : ↥(GammaHUpper (M * q) H' ℓ) →* Multiplicative 𝒪 :=
    (AddMonoidHom.toMultiplicativeRight ψ).comp (conjL (M * q) H' ℓ)
  have hchar : χ₂.comp (restrictEquiv e _ _ hHℓ) =
      (AddMonoidHom.toMultiplicativeRight (wOp hH' h1 hcop ht 𝒪 ψ)).comp (conjL (M * q) H' ℓ) := by
    ext k
    simp only [χ₂, MonoidHom.comp_apply, AddMonoidHom.toMultiplicativeRight_apply_apply]
    apply congrArg Multiplicative.ofAdd
    show ψ (Additive.ofMul (conjL (M * q) H' ℓ (restrictEquiv e _ _ hHℓ k))) =
      ψ (Additive.ofMul (alHom hH' h1 hcop ht (conjL (M * q) H' ℓ k)))
    have hk : restrictEquiv e _ _ hHℓ k = ⟨alHom hH' h1 hcop ht (k : ↥(GammaH (M * q) H')),
        alHom_mem_upper hH' h1 hcop ht ℓ ht' hℓt k⟩ := Subtype.ext rfl
    obtain ⟨r, hr⟩ := alHom_eq_conj hH' h1 hcop ht ht' (conjL (M * q) H' ℓ k)
    rw [hk, conjL_alHom hH' h1 hcop ht ℓ ht' hℓt k, hr, apply_conj]
  refine AddMonoidHom.ext fun a => ?_
  show Multiplicative.toAdd (MonoidHom.transfer χ₂ (e (Additive.toMul a))) =
    Multiplicative.toAdd (MonoidHom.transfer
      ((AddMonoidHom.toMultiplicativeRight (wOp hH' h1 hcop ht 𝒪 ψ)).comp (conjL (M * q) H' ℓ))
      (Additive.toMul a))
  rw [← hchar, transfer_comp_equiv]

end HeckeComm
p2m_reactivate "P2MW.S_CohCarrier_exists_atkinLehnerOp_iDegL_jDegL_five_identities_of_prime.AtkinLehnerH1Sol.IsAL"

section Index

theorem range_eq_map_upper :
    (iotaDeg M (M * q) H H' 1 h1).range =
      (GammaHUpper M H q).map (MulAut.conj (tW H ht)).toMonoidHom := by
  ext x
  rw [Subgroup.mem_map, mem_range_one_iff hH' h1]
  constructor
  · intro hx
    refine ⟨(tW H ht)⁻¹ * x * tW H ht, ?_, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
    rw [Subgroup.mem_subgroupOf, mem_Gamma0Upper, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact ht.dvd_conj_inv_01 _ (dvd_trans (by push_cast; exact dvd_mul_left _ _)
      ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hx)))
  · rintro ⟨k, hk, rfl⟩
    rw [Subgroup.mem_subgroupOf, mem_Gamma0Upper, ZMod.intCast_zmod_eq_zero_iff_dvd] at hk
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact ht.conj_mem_Gamma0 hcop _ ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      (Gamma0_mem.mp (GammaH_le_Gamma0 H k.2))) hk

theorem index_range_one (hq : q.Prime) (hqM : ¬ q ∣ M) :
    (iotaDeg M (M * q) H H' 1 h1).range.index = q + 1 := by
  rw [range_eq_map_upper hH' h1 hcop ht, Subgroup.index_map_of_bijective (MulAut.conj (tW H ht)).bijective]
  exact CohCarrier.index_GammaHUpper_of_prime M H q hq hqM

theorem gammaHLower_le_range : GammaHLower M H q ≤ (iotaDeg M (M * q) H H' 1 h1).range := by
  intro x hx
  rw [mem_range_one_iff hH' h1, mul_comm]
  exact Subgroup.mem_subgroupOf.mp hx

end Index
p2m_reactivate "P2MW.S_CohCarrier_exists_atkinLehnerOp_iDegL_jDegL_five_identities_of_prime.AtkinLehnerH1Sol.IsAL"

section Diamonds

omit hH' h1 hcop ht

theorem diamondRaw_mul {N : ℕ} {K : Subgroup (ZMod N)ˣ} (σ τ : ↥(Gamma0 N)) (φ : H1 N K 𝒪) :
    diamondRaw N K 𝒪 (σ * τ) φ = diamondRaw N K 𝒪 τ (diamondRaw N K 𝒪 σ φ) := by
  refine AddMonoidHom.ext fun a => ?_
  show φ (Additive.ofMul (conjHom N K (σ * τ) (Additive.toMul a))) =
    φ (Additive.ofMul (conjHom N K σ (conjHom N K τ (Additive.toMul a))))
  have : conjHom N K (σ * τ) (Additive.toMul a) = conjHom N K σ (conjHom N K τ (Additive.toMul a)) := by
    apply Subtype.ext
    simp only [conjHom, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_mul, mul_inv_rev]
    group
  rw [this]

theorem diamondRaw_eq_self_of_mem {N : ℕ} {K : Subgroup (ZMod N)ˣ} (σ : ↥(Gamma0 N))
    (hσ : (σ : SL(2, ℤ)) ∈ GammaH N K) (φ : H1 N K 𝒪) : diamondRaw N K 𝒪 σ φ = φ := by
  refine AddMonoidHom.ext fun a => ?_
  show φ (Additive.ofMul (conjHom N K σ (Additive.toMul a))) = φ a
  have : conjHom N K σ (Additive.toMul a) = ⟨σ, hσ⟩ * Additive.toMul a * ⟨σ, hσ⟩⁻¹ := Subtype.ext rfl
  rw [this, apply_conj]
  rfl

theorem eq_of_mul_q_eq_one {R : Type*} [CommMonoid R] {x y c : R} (hx : x * c = 1) (hy : y * c = 1) :
    x = y := by
  rw [← mul_one x, ← hy, mul_left_comm, hx, mul_one]

end Diamonds
p2m_reactivate "P2MW.S_CohCarrier_exists_atkinLehnerOp_iDegL_jDegL_five_identities_of_prime.AtkinLehnerH1Sol.IsAL"

end AL
p2m_reactivate "P2MW.S_CohCarrier_exists_atkinLehnerOp_iDegL_jDegL_five_identities_of_prime.AtkinLehnerH1Sol.IsAL"

end Level
p2m_reactivate "P2MW.S_CohCarrier_exists_atkinLehnerOp_iDegL_jDegL_five_identities_of_prime.AtkinLehnerH1Sol.IsAL"

section Main

open CohCarrier CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups

theorem main (M q : ℕ) [NeZero M] [NeZero q] (hq : q.Prime) (hqM : ¬ q ∣ M)
    (H : Subgroup (ZMod M)ˣ) (H' : Subgroup (ZMod (M * q))ˣ)
    (hH' : ∀ v : (ZMod (M * q))ˣ, v ∈ H' ↔ ZMod.unitsMap (dvd_mul_right M q) v ∈ H)
    (h1 : CohCarrier.LevelLE M (M * q) H H' 1)
    (𝒪 : Type) [CommRing 𝒪] :
    haveI : NeZero (M * q) := ⟨mul_ne_zero (NeZero.ne M) (NeZero.ne q)⟩
    ∃ (u : (ZMod (M * q))ˣ) (w : Module.End 𝒪 (CohCarrier.H1 (M * q) H' 𝒪)),
      (ZMod.unitsMap (dvd_mul_right M q) u : ZMod M) * (q : ZMod M) = 1 ∧
      w ∘ₗ CohCarrier.iDegL M (M * q) H H' 1 𝒪 𝒪 h1 =
        (CohCarrier.iDegL M (M * q) H H' 1 𝒪 𝒪 h1 ∘ₗ CohCarrier.heckeTL M H 𝒪 q -
            CohCarrier.heckeTL (M * q) H' 𝒪 q ∘ₗ CohCarrier.iDegL M (M * q) H H' 1 𝒪 𝒪 h1) ∘ₗ
          CohCarrier.diamondL M H 𝒪 (ZMod.unitsMap (dvd_mul_right M q) u) ∧
      CohCarrier.jDegL M (M * q) H H' 1 𝒪 𝒪 h1 ∘ₗ CohCarrier.iDegL M (M * q) H H' 1 𝒪 𝒪 h1 =
        ((q : 𝒪) + 1) • LinearMap.id ∧
      CohCarrier.jDegL M (M * q) H H' 1 𝒪 𝒪 h1 ∘ₗ w ∘ₗ CohCarrier.iDegL M (M * q) H H' 1 𝒪 𝒪 h1 =
        CohCarrier.heckeTL M H 𝒪 q *
          CohCarrier.diamondL M H 𝒪 (ZMod.unitsMap (dvd_mul_right M q) u) ∧
      CohCarrier.iDegL M (M * q) H H' 1 𝒪 𝒪 h1 ∘ₗ CohCarrier.jDegL M (M * q) H H' 1 𝒪 𝒪 h1 =
        LinearMap.id + CohCarrier.heckeTL (M * q) H' 𝒪 q * w ∧
      w * w = CohCarrier.diamondL (M * q) H' 𝒪 u ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ≠ q →
        w * (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; CohCarrier.heckeTL (M * q) H' 𝒪 ℓ) =
          (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; CohCarrier.heckeTL (M * q) H' 𝒪 ℓ) * w) ∧
      (∀ v : (ZMod (M * q))ˣ,
        w * CohCarrier.diamondL (M * q) H' 𝒪 v = CohCarrier.diamondL (M * q) H' 𝒪 v * w) := by
  haveI hMq : NeZero (M * q) := ⟨mul_ne_zero (NeZero.ne M) (NeZero.ne q)⟩
  have hcopN : Nat.Coprime q M := (Nat.Prime.coprime_iff_not_dvd hq).mpr hqM
  have hcop : IsCoprime (M : ℤ) (q : ℤ) := (Nat.isCoprime_iff_coprime.mpr hcopN).symm
  obtain ⟨u₀, v₀, huv⟩ : IsCoprime (q : ℤ) (M : ℤ) := hcop.symm
  have ht₀ : IsAL M q (tB u₀ v₀ huv) := isAL_tB u₀ v₀ huv
  set u : (ZMod (M * q))ˣ := gamma0Units (M * q) (gamma0Sq hcop ht₀) with hu
  have hu1 : (ZMod.unitsMap (dvd_mul_right M q) u : ZMod M) * (q : ZMod M) = 1 :=
    unitsMap_gamma0Sq_mul_q hH' h1 hcop ht₀

  set σ₀ : Gamma0 M := Classical.choose (gamma0Units_surjective M (ZMod.unitsMap (dvd_mul_right M q) u))
    with hσ₀
  have hσ₀u : gamma0Units M σ₀ = ZMod.unitsMap (dvd_mul_right M q) u :=
    Classical.choose_spec (gamma0Units_surjective M (ZMod.unitsMap (dvd_mul_right M q) u))
  have hD : ∀ φ : H1 M H 𝒪, diamondL M H 𝒪 (ZMod.unitsMap (dvd_mul_right M q) u) φ =
      diamondRaw M H 𝒪 σ₀ φ := fun φ => rfl
  refine ⟨u, wOp hH' h1 hcop ht₀ 𝒪, hu1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    obtain ⟨σ, hσ, hA⟩ := CohCarrier.exists_gamma0_heckeT_iDeg_interchange_diamondRaw (A := 𝒪)
      hq hqM H H' h1 (levelLE_q hH')
    refine LinearMap.ext fun φ => ?_
    show wOp hH' h1 hcop ht₀ 𝒪 (iDeg' M (M * q) H H' 1 𝒪 h1 φ) =
      iDeg' M (M * q) H H' 1 𝒪 h1 (heckeT M H q 𝒪
          (diamondL M H 𝒪 (ZMod.unitsMap (dvd_mul_right M q) u) φ)) -
        heckeT (M * q) H' q 𝒪 (iDeg' M (M * q) H H' 1 𝒪 h1
          (diamondL M H 𝒪 (ZMod.unitsMap (dvd_mul_right M q) u) φ))
    rw [wOp_iDeg, hA, sub_sub_cancel, hD, ← diamondRaw_mul, diamondRaw_eq_self_of_mem]
    refine mem_GammaH_iff.mpr ⟨(σ₀ * σ).2, ?_⟩
    rw [Subtype.coe_eta, map_mul, hσ₀u]
    have hprod : ZMod.unitsMap (dvd_mul_right M q) u * gamma0Units M σ = 1 := by
      apply Units.ext
      rw [Units.val_mul, val_gamma0Units, Units.val_one]
      show (ZMod.unitsMap (dvd_mul_right M q) u : ZMod M) * (((σ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) = 1
      rw [hσ]
      exact hu1
    rw [hprod]
    exact H.one_mem
  ·
    refine LinearMap.ext fun φ => ?_
    show jDeg M (M * q) H H' 1 𝒪 h1 (iDeg' M (M * q) H H' 1 𝒪 h1 φ) = ((q : 𝒪) + 1) • φ
    rw [CohCarrier.jDeg_comp_iDegP_self h1 φ, index_range_one hH' h1 hcop ht₀ hq hqM,
      show ((q : 𝒪) + 1) = ((q + 1 : ℕ) : 𝒪) by push_cast; ring, Nat.cast_smul_eq_nsmul]
  ·
    obtain ⟨τ, hτ, hB⟩ := CohCarrier.exists_gamma0_heckeTlower_eq_heckeT_diamondRaw (A := 𝒪) hq hqM H
    refine LinearMap.ext fun φ => ?_
    show jDeg M (M * q) H H' 1 𝒪 h1 (wOp hH' h1 hcop ht₀ 𝒪 (iDeg' M (M * q) H H' 1 𝒪 h1 φ)) =
      heckeT M H q 𝒪 (diamondL M H 𝒪 (ZMod.unitsMap (dvd_mul_right M q) u) φ)
    have hdqM : ((1 * q : ℕ) : ℤ) ∣ ((M * q : ℕ) : ℤ) := by push_cast; exact ⟨M, by ring⟩
    rw [wOp_iDeg, CohCarrier.jDeg_iDeg_cross_eq_index_smul_heckeTlower hq hqM h1 (levelLE_q hH')
      hdqM (one_mul q).symm φ, Subgroup.subgroupOf_eq_top.mpr (gammaHLower_le_range hH' h1 hcop ht₀),
      Subgroup.index_top, one_smul, hB φ]
    congr 1
    refine (diamondL_eq_diamondRaw M H 𝒪 _ τ ?_ φ).symm
    apply Units.ext
    rw [val_gamma0Units]
    show (((τ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) = _
    refine eq_of_mul_q_eq_one (c := (q : ZMod M)) ?_ hu1
    rw [← hτ]
    exact Gamma0_d_mul_a M τ
  ·
    refine LinearMap.ext fun ψ => ?_
    exact iDeg_jDeg hH' h1 hcop ht₀ 𝒪 hq ψ
  ·
    refine LinearMap.ext fun ψ => ?_
    show wOp hH' h1 hcop ht₀ 𝒪 (wOp hH' h1 hcop ht₀ 𝒪 ψ) = diamondL (M * q) H' 𝒪 u ψ
    rw [wOp_wOp]
    exact (diamondL_eq_diamondRaw (M * q) H' 𝒪 u (gamma0Sq hcop ht₀) rfl ψ).symm
  ·
    intro ℓ hℓ hℓq
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    have hcop' : IsCoprime (q : ℤ) ((ℓ * M : ℕ) : ℤ) := by
      rw [Nat.isCoprime_iff_coprime, Nat.Prime.coprime_iff_not_dvd hq]
      intro hdvd
      rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | h
      · exact hℓq ((Nat.prime_dvd_prime_iff_eq hq hℓ).mp h).symm
      · exact hqM h
    obtain ⟨u', v', huv'⟩ := hcop'
    have huv'' : u' * q + v' * (ℓ * M) = 1 := by push_cast at huv'; linear_combination huv'
    have htℓ : IsAL M q (tB u' (v' * ℓ) (tB_huv ℓ u' v' huv'')) := isAL_tB _ _ _
    have htℓ' : IsAL M q (tC ℓ u' v' huv'') := isAL_tC ℓ u' v' huv''
    rw [wOp_eq_of_isAL hH' h1 hcop ht₀ 𝒪 htℓ]
    refine LinearMap.ext fun ψ => ?_
    exact wOp_heckeT hH' h1 hcop htℓ 𝒪 ℓ htℓ' (aMat_mul_tB ℓ u' v' huv'').symm ψ
  ·
    intro v
    refine LinearMap.ext fun ψ => ?_
    exact wOp_diamondRaw hH' h1 hcop ht₀ 𝒪 _ ψ

end Main
p2m_reactivate "P2MW.S_CohCarrier_exists_atkinLehnerOp_iDegL_jDegL_five_identities_of_prime.AtkinLehnerH1Sol.IsAL"

end AtkinLehnerH1Sol
p2m_reactivate "P2MW.S_CohCarrier_exists_atkinLehnerOp_iDegL_jDegL_five_identities_of_prime.AtkinLehnerH1Sol.IsAL P2MW.S_CohCarrier_exists_atkinLehnerOp_iDegL_jDegL_five_identities_of_prime.AtkinLehnerH1Sol"

open CohCarrier

theorem solution
    (M q : ℕ) [NeZero M] [NeZero q] (hq : q.Prime) (hqM : ¬ q ∣ M)
    (H : Subgroup (ZMod M)ˣ) (H' : Subgroup (ZMod (M * q))ˣ)
    (hH' : ∀ v : (ZMod (M * q))ˣ, v ∈ H' ↔ ZMod.unitsMap (dvd_mul_right M q) v ∈ H)
    (h1 : CohCarrier.LevelLE M (M * q) H H' 1)
    (𝒪 : Type) [CommRing 𝒪] :
    haveI : NeZero (M * q) := ⟨mul_ne_zero (NeZero.ne M) (NeZero.ne q)⟩
    ∃ (u : (ZMod (M * q))ˣ) (w : Module.End 𝒪 (CohCarrier.H1 (M * q) H' 𝒪)),

      (ZMod.unitsMap (dvd_mul_right M q) u : ZMod M) * (q : ZMod M) = 1 ∧

      w ∘ₗ CohCarrier.iDegL M (M * q) H H' 1 𝒪 𝒪 h1 =
        (CohCarrier.iDegL M (M * q) H H' 1 𝒪 𝒪 h1 ∘ₗ CohCarrier.heckeTL M H 𝒪 q -
            CohCarrier.heckeTL (M * q) H' 𝒪 q ∘ₗ CohCarrier.iDegL M (M * q) H H' 1 𝒪 𝒪 h1) ∘ₗ
          CohCarrier.diamondL M H 𝒪 (ZMod.unitsMap (dvd_mul_right M q) u) ∧

      CohCarrier.jDegL M (M * q) H H' 1 𝒪 𝒪 h1 ∘ₗ CohCarrier.iDegL M (M * q) H H' 1 𝒪 𝒪 h1 =
        ((q : 𝒪) + 1) • LinearMap.id ∧

      CohCarrier.jDegL M (M * q) H H' 1 𝒪 𝒪 h1 ∘ₗ w ∘ₗ CohCarrier.iDegL M (M * q) H H' 1 𝒪 𝒪 h1 =
        CohCarrier.heckeTL M H 𝒪 q *
          CohCarrier.diamondL M H 𝒪 (ZMod.unitsMap (dvd_mul_right M q) u) ∧

      CohCarrier.iDegL M (M * q) H H' 1 𝒪 𝒪 h1 ∘ₗ CohCarrier.jDegL M (M * q) H H' 1 𝒪 𝒪 h1 =
        LinearMap.id + CohCarrier.heckeTL (M * q) H' 𝒪 q * w ∧

      w * w = CohCarrier.diamondL (M * q) H' 𝒪 u ∧

      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ≠ q →
        w * (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; CohCarrier.heckeTL (M * q) H' 𝒪 ℓ) =
          (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; CohCarrier.heckeTL (M * q) H' 𝒪 ℓ) * w) ∧
      (∀ v : (ZMod (M * q))ˣ,
        w * CohCarrier.diamondL (M * q) H' 𝒪 v = CohCarrier.diamondL (M * q) H' 𝒪 v * w) :=
  AtkinLehnerH1Sol.main M q hq hqM H H' hH' h1 𝒪

end S_CohCarrier_exists_atkinLehnerOp_iDegL_jDegL_five_identities_of_prime
end P2MW
export P2MW.S_CohCarrier_exists_atkinLehnerOp_iDegL_jDegL_five_identities_of_prime (solution)
