-- Prove2me | solution 1 for CohCarrier.heckeT_heckeT_eq_self_of_jDeg_one_eq_zero_of_jDeg_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/1d609d5a-566f-5cdc-82c3-1f3d4654b1f4

import Mathlib
import Definitions.Def_CohCarrier_Lower
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_heckeT_heckeT_eq_self_of_jDeg_one_eq_zero_of_jDeg_eq_zero

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ALInvolSol

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

theorem index_eq_of_equiv (e : G ≃* G₂) (H : Subgroup G) (H₂ : Subgroup G₂)
    (hH : ∀ x, x ∈ H ↔ e x ∈ H₂) : H.index = H₂.index := by
  rw [Subgroup.index_eq_card, Subgroup.index_eq_card]
  exact Nat.card_congr (quotEquiv e H H₂ hH)

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

end Naturality

section Mackey

variable {G : Type*} [Group G] {C : Type*} [CommGroup C]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

def stabSub (H : Subgroup G) (w : G) : Subgroup ↥H where
  carrier := {h | w * (h : G) * w⁻¹ ∈ H}
  one_mem' := by simp [H.one_mem]
  mul_mem' := by
    intro a b ha hb
    have : w * ((a * b : ↥H) : G) * w⁻¹ = (w * (a : G) * w⁻¹) * (w * (b : G) * w⁻¹) := by
      simp only [Subgroup.coe_mul]; group
    show w * ((a * b : ↥H) : G) * w⁻¹ ∈ H
    rw [this]; exact H.mul_mem ha hb
  inv_mem' := by
    intro a ha
    have : w * ((a⁻¹ : ↥H) : G) * w⁻¹ = (w * (a : G) * w⁻¹)⁻¹ := by
      simp only [Subgroup.coe_inv]; group
    show w * ((a⁻¹ : ↥H) : G) * w⁻¹ ∈ H
    rw [this]; exact H.inv_mem ha

theorem mem_stabSub_iff (H : Subgroup G) (w : G) (h : ↥H) :
    h ∈ stabSub H w ↔ w * (h : G) * w⁻¹ ∈ H := Iff.rfl

def conjIn (H : Subgroup G) (w : G) : ↥(stabSub H w) →* ↥H where
  toFun k := ⟨w * ((k : ↥H) : G) * w⁻¹, k.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by
    simp only [Subgroup.coe_mul]
    group)

@[scoped simp] theorem coe_conjIn (H : Subgroup G) (w : G) (k : ↥(stabSub H w)) :
    ((conjIn H w k : ↥H) : G) = w * ((k : ↥H) : G) * w⁻¹ := rfl

def optMap (H : Subgroup G) (w : G) : Option (↥H ⧸ stabSub H w) → G ⧸ H :=
  fun o => o.elim (QuotientGroup.mk 1)
    (Quotient.map' (fun h : ↥H => (h : G) * w⁻¹) (fun a b hab => by
      rw [QuotientGroup.leftRel_apply] at hab ⊢
      rw [mem_stabSub_iff, Subgroup.coe_mul, Subgroup.coe_inv] at hab
      have : ((a : G) * w⁻¹)⁻¹ * ((b : G) * w⁻¹) = w * ((a : G)⁻¹ * b) * w⁻¹ := by group
      rw [this]; exact hab))

theorem optMap_none (H : Subgroup G) (w : G) : optMap H w none = QuotientGroup.mk 1 := rfl

theorem optMap_some_mk (H : Subgroup G) (w : G) (h : ↥H) :
    optMap H w (some (QuotientGroup.mk h)) = QuotientGroup.mk ((h : G) * w⁻¹) := rfl

theorem optMap_some_smul (H : Subgroup G) (w : G) (y : ↥H) (p : ↥H ⧸ stabSub H w) :
    optMap H w (some (y • p)) = (y : G) • optMap H w (some p) := by
  induction p using Quotient.inductionOn' with | h a => ?_
  change optMap H w (some (y • QuotientGroup.mk a)) = (y : G) • optMap H w (some (QuotientGroup.mk a))
  rw [MulAction.Quotient.smul_mk, optMap_some_mk, optMap_some_mk, MulAction.Quotient.smul_mk,
    smul_eq_mul, smul_eq_mul, Subgroup.coe_mul, mul_assoc]

theorem optMap_bijective (H : Subgroup G) (w : G)
    (hdec : ∀ g : G, g ∈ H ∨ ∃ l ∈ H, w * l⁻¹ * g ∈ H) (hnot : w ∉ H) :
    Function.Bijective (optMap H w) := by
  constructor
  · rintro (_ | a) (_ | b) hab
    · rfl
    · exfalso
      induction b using Quotient.inductionOn' with | h b => ?_
      change (QuotientGroup.mk 1 : G ⧸ H) = QuotientGroup.mk ((b : G) * w⁻¹) at hab
      rw [QuotientGroup.eq, inv_one, one_mul] at hab
      have : w ∈ H := by
        have := H.inv_mem (H.mul_mem (H.inv_mem b.2) hab)
        simpa using this
      exact hnot this
    · exfalso
      induction a using Quotient.inductionOn' with | h a => ?_
      change QuotientGroup.mk ((a : G) * w⁻¹) = (QuotientGroup.mk 1 : G ⧸ H) at hab
      rw [QuotientGroup.eq, mul_one] at hab
      have : w ∈ H := by
        have := H.mul_mem hab a.2
        simpa using this
      exact hnot this
    · induction a using Quotient.inductionOn' with | h a => ?_
      induction b using Quotient.inductionOn' with | h b => ?_
      change QuotientGroup.mk ((a : G) * w⁻¹) = (QuotientGroup.mk ((b : G) * w⁻¹) : G ⧸ H) at hab
      rw [QuotientGroup.eq] at hab
      change some (QuotientGroup.mk a : ↥H ⧸ stabSub H w) = some (QuotientGroup.mk b)
      rw [Option.some_inj, QuotientGroup.eq, mem_stabSub_iff, Subgroup.coe_mul, Subgroup.coe_inv]
      have : w * ((a : G)⁻¹ * b) * w⁻¹ = ((a : G) * w⁻¹)⁻¹ * ((b : G) * w⁻¹) := by group
      rw [this]; exact hab
  · intro Q
    induction Q using Quotient.inductionOn' with | h g => ?_
    rcases hdec g with hg | ⟨l, hl, hlg⟩
    · exact ⟨none, by
        change (QuotientGroup.mk 1 : G ⧸ H) = QuotientGroup.mk g
        rw [QuotientGroup.eq, inv_one, one_mul]; exact hg⟩
    · exact ⟨some (QuotientGroup.mk ⟨l, hl⟩), by
        change (QuotientGroup.mk (l * w⁻¹) : G ⧸ H) = QuotientGroup.mk g
        rw [QuotientGroup.eq]
        have : (l * w⁻¹)⁻¹ * g = w * l⁻¹ * g := by group
        rw [this]; exact hlg⟩

theorem transfer_mackey_same (H : Subgroup G) [H.FiniteIndex] (w : G)
    [(stabSub H w).FiniteIndex]
    (hdec : ∀ g : G, g ∈ H ∨ ∃ l ∈ H, w * l⁻¹ * g ∈ H) (hnot : w ∉ H)
    (χ : ↥H →* C) (x : ↥H) :
    MonoidHom.transfer χ (x : G)
      = χ x * MonoidHom.transfer (χ.comp (conjIn H w)) x := by
  set E : Option (↥H ⧸ stabSub H w) ≃ G ⧸ H :=
    Equiv.ofBijective (optMap H w) (optMap_bijective H w hdec hnot) with hE
  have hEa : ∀ o, E o = optMap H w o := fun o => rfl

  let s : ↥H ⧸ stabSub H w → ↥H := Quotient.out
  have hs : ∀ p, (s p : ↥H ⧸ stabSub H w) = p := fun p => Quotient.out_eq p
  let f : G ⧸ H → G := fun Q => (E.symm Q).elim 1 (fun p => ((s p : ↥H) : G) * w⁻¹)
  have hf : ∀ Q, (f Q : G ⧸ H) = Q := by
    intro Q
    obtain ⟨o, rfl⟩ := E.surjective Q
    simp only [f, Equiv.symm_apply_apply]
    cases o with
    | none => rfl
    | some p =>
        change QuotientGroup.mk (((s p : ↥H) : G) * w⁻¹) = E (some p)
        rw [hEa]
        conv_rhs => rw [← hs p]
        rfl
  rw [transfer_eq_prod_section χ f hf, transfer_eq_prod_section _ s hs,
    ← Fintype.prod_equiv E _ _ (fun _ => rfl), Fintype.prod_option]
  congr 1
  · refine congrArg χ (Subtype.ext ?_)
    have h1 : (x : G)⁻¹ • E none = E none := by
      rw [hEa, optMap_none, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.eq,
        inv_inv, mul_one]
      exact x.2
    simp only [f, h1, Equiv.symm_apply_apply, Option.elim, inv_one, one_mul, mul_one]
  · refine Finset.prod_congr rfl (fun p _ => ?_)
    rw [MonoidHom.comp_apply]
    refine congrArg χ (Subtype.ext ?_)
    have h1 : (x : G)⁻¹ • E (some p) = E (some (x⁻¹ • p)) := by
      rw [hEa, hEa, optMap_some_smul, Subgroup.coe_inv]
    simp only [coe_conjIn, Subgroup.coe_mul, Subgroup.coe_inv, f, h1,
      Equiv.symm_apply_apply, Option.elim]
    group

end Mackey

section Concrete

open CohCarrier CongruenceSubgroup
open scoped MatrixGroups

variable {M q : ℕ} [NeZero M] [NeZero q]

@[scoped simp] theorem conjLowerMat_apply_00 (d : ℕ) (A : SL(2, ℤ)) (h : (d : ℤ) ∣ A 1 0) :
    (conjLowerMat d A h) 0 0 = A 0 0 := by
  simp [conjLowerMat]

@[scoped simp] theorem conjLowerMat_apply_01 (d : ℕ) (A : SL(2, ℤ)) (h : (d : ℤ) ∣ A 1 0) :
    (conjLowerMat d A h) 0 1 = A 0 1 * d := by
  simp [conjLowerMat]

@[scoped simp] theorem conjLowerMat_apply_10 (d : ℕ) (A : SL(2, ℤ)) (h : (d : ℤ) ∣ A 1 0) :
    (conjLowerMat d A h) 1 0 = A 1 0 / d := by
  simp [conjLowerMat]

@[scoped simp] theorem conjLowerMat_apply_11 (d : ℕ) (A : SL(2, ℤ)) (h : (d : ℤ) ∣ A 1 0) :
    (conjLowerMat d A h) 1 1 = A 1 1 := by
  simp [conjLowerMat]

theorem mem_range_iotaDeg_one_iff
    (h1 : LevelLE M (M * q) (⊤ : Subgroup (ZMod M)ˣ) (⊤ : Subgroup (ZMod (M * q))ˣ) 1)
    (x : ↥(GammaH M ⊤)) :
    x ∈ (iotaDeg M (M * q) ⊤ ⊤ 1 h1).range ↔ (x : SL(2, ℤ)) ∈ Gamma0 (M * q) := by
  constructor
  · rintro ⟨g, rfl⟩
    rw [coe_iotaDeg_one h1 g, ← GammaH_top]
    exact g.2
  · intro hx
    refine ⟨⟨(x : SL(2, ℤ)), by rw [GammaH_top]; exact hx⟩, Subtype.ext ?_⟩
    exact coe_iotaDeg_one h1 _

theorem mem_range_iotaDeg_q_iff
    (hq' : LevelLE M (M * q) (⊤ : Subgroup (ZMod M)ˣ) (⊤ : Subgroup (ZMod (M * q))ˣ) q)
    (x : ↥(GammaH M ⊤)) :
    x ∈ (iotaDeg M (M * q) ⊤ ⊤ q hq').range ↔ (q : ℤ) ∣ (x : SL(2, ℤ)) 0 1 := by
  constructor
  · rintro ⟨g, rfl⟩
    show (q : ℤ) ∣ (conjLowerMat q (g : SL(2, ℤ)) (hq'.dvd_entry g)) 0 1
    rw [conjLowerMat_apply_01]
    exact dvd_mul_left _ _
  · intro hdiv
    have hxM : (M : ℤ) ∣ (x : SL(2, ℤ)) 1 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp (GammaH_le_Gamma0 ⊤ x.2))
    have hmem : conjUpperMat q (x : SL(2, ℤ)) hdiv ∈ GammaH (M * q) ⊤ := by
      rw [GammaH_top, Gamma0_mem, conjUpperMat_apply_10, ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      exact mul_dvd_mul hxM (dvd_refl _)
    refine ⟨⟨conjUpperMat q (x : SL(2, ℤ)) hdiv, hmem⟩, Subtype.ext ?_⟩
    exact conjLowerMat_conjUpperMat q (x : SL(2, ℤ)) hdiv
      (hq'.dvd_entry ⟨conjUpperMat q (x : SL(2, ℤ)) hdiv, hmem⟩)

theorem iotaDeg_q_conjL
    (h1 : LevelLE M (M * q) (⊤ : Subgroup (ZMod M)ˣ) (⊤ : Subgroup (ZMod (M * q))ˣ) 1)
    (hq' : LevelLE M (M * q) (⊤ : Subgroup (ZMod M)ˣ) (⊤ : Subgroup (ZMod (M * q))ˣ) q)
    (k : ↥(GammaHUpper (M * q) ⊤ q)) :
    iotaDeg M (M * q) ⊤ ⊤ q hq' (conjL (M * q) ⊤ q k) = iotaDeg M (M * q) ⊤ ⊤ 1 h1 k := by
  apply Subtype.ext
  rw [coe_iotaDeg_one h1]
  exact conjLowerMat_conjUpperMat q ((k : ↥(GammaH (M * q) ⊤)) : SL(2, ℤ))
    (dvd_of_mem_GammaHUpper (M * q) ⊤ q k) (hq'.dvd_entry (conjL (M * q) ⊤ q k))

def wMat (u v : ℤ) (huv : u * q + v * M = 1) : SL(2, ℤ) :=
  ⟨!![u, -v; (M : ℤ), (q : ℤ)], by rw [Matrix.det_fin_two_of]; linear_combination huv⟩

theorem wMat_mem (u v : ℤ) (huv : u * q + v * M = 1) : wMat (M := M) (q := q) u v huv ∈ GammaH M ⊤ := by
  rw [GammaH_top, Gamma0_mem]
  show (((M : ℤ)) : ZMod M) = 0
  rw [Int.cast_natCast, ZMod.natCast_self]

def wElt (u v : ℤ) (huv : u * q + v * M = 1) : ↥(GammaH M ⊤) := ⟨wMat u v huv, wMat_mem u v huv⟩

section entries

variable (u v : ℤ) (huv : u * q + v * M = 1)

theorem mul_apply' (x y : SL(2, ℤ)) (i j : Fin 2) :
    (x * y : SL(2, ℤ)) i j = x i 0 * y 0 j + x i 1 * y 1 j := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem inv_apply' (x : SL(2, ℤ)) :
    (x⁻¹ : SL(2, ℤ)) 0 0 = x 1 1 ∧ (x⁻¹ : SL(2, ℤ)) 0 1 = -x 0 1 ∧
      (x⁻¹ : SL(2, ℤ)) 1 0 = -x 1 0 ∧ (x⁻¹ : SL(2, ℤ)) 1 1 = x 0 0 := by
  simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

@[scoped simp] theorem wMat_00 : (wMat (M := M) (q := q) u v huv) 0 0 = u := rfl
@[scoped simp] theorem wMat_01 : (wMat (M := M) (q := q) u v huv) 0 1 = -v := rfl
@[scoped simp] theorem wMat_10 : (wMat (M := M) (q := q) u v huv) 1 0 = M := rfl
@[scoped simp] theorem wMat_11 : (wMat (M := M) (q := q) u v huv) 1 1 = q := rfl

theorem wMat_inv_00 : ((wMat (M := M) (q := q) u v huv)⁻¹ : SL(2, ℤ)) 0 0 = q := by
  rw [(inv_apply' _).1, wMat_11]

theorem wMat_inv_01 : ((wMat (M := M) (q := q) u v huv)⁻¹ : SL(2, ℤ)) 0 1 = v := by
  rw [(inv_apply' _).2.1, wMat_01, neg_neg]

theorem winv_x_w_01 (x : SL(2, ℤ)) :
    ((wMat (M := M) (q := q) u v huv)⁻¹ * x * wMat (M := M) (q := q) u v huv : SL(2, ℤ)) 0 1
      = q * (q * x 0 1 + v * x 1 1 - x 0 0 * v) - v ^ 2 * x 1 0 := by
  rw [mul_apply', mul_apply', mul_apply', wMat_inv_00, wMat_inv_01, wMat_01, wMat_11]
  ring

theorem winv_g_01 (g : SL(2, ℤ)) :
    ((wMat (M := M) (q := q) u v huv)⁻¹ * g : SL(2, ℤ)) 0 1 = q * g 0 1 + v * g 1 1 := by
  rw [mul_apply', wMat_inv_00, wMat_inv_01]

theorem linv_w_01 (l : SL(2, ℤ)) :
    (l⁻¹ * wMat (M := M) (q := q) u v huv : SL(2, ℤ)) 0 1 = -(l 1 1 * v + l 0 1 * q) := by
  rw [mul_apply', (inv_apply' l).1, (inv_apply' l).2.1, wMat_01, wMat_11]
  ring

theorem uinv_g_01 (t : ℤ) (g : SL(2, ℤ)) :
    ((uMat t)⁻¹ * g : SL(2, ℤ)) 0 1 = g 0 1 - t * g 1 1 := by
  rw [mul_apply', (inv_apply' (uMat t)).1, (inv_apply' (uMat t)).2.1, uMat_apply_11, uMat_apply_01]
  ring

end entries

theorem hw_wElt (u v : ℤ) (huv : u * q + v * M = 1)
    (h1 : LevelLE M (M * q) (⊤ : Subgroup (ZMod M)ˣ) (⊤ : Subgroup (ZMod (M * q))ˣ) 1)
    (hq' : LevelLE M (M * q) (⊤ : Subgroup (ZMod M)ˣ) (⊤ : Subgroup (ZMod (M * q))ˣ) q)
    (x : ↥(GammaH M ⊤)) :
    x ∈ (iotaDeg M (M * q) ⊤ ⊤ 1 h1).range ↔
      (wElt u v huv)⁻¹ * x * wElt u v huv ∈ (iotaDeg M (M * q) ⊤ ⊤ q hq').range := by
  rw [mem_range_iotaDeg_one_iff, mem_range_iotaDeg_q_iff, Gamma0_mem,
    ZMod.intCast_zmod_eq_zero_iff_dvd]
  show ((M * q : ℕ) : ℤ) ∣ (x : SL(2, ℤ)) 1 0 ↔
    (q : ℤ) ∣ ((wMat (M := M) (q := q) u v huv)⁻¹ * (x : SL(2, ℤ)) * wMat (M := M) (q := q) u v huv
      : SL(2, ℤ)) 0 1
  rw [winv_x_w_01, dvd_sub_right (dvd_mul_right _ _)]
  have hxM : (M : ℤ) ∣ (x : SL(2, ℤ)) 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp (GammaH_le_Gamma0 ⊤ x.2))
  have hqM : IsCoprime (q : ℤ) (M : ℤ) := ⟨u, v, huv⟩
  have hqv : IsCoprime (q : ℤ) (v ^ 2) :=
    IsCoprime.pow_right ⟨u, M, by linear_combination huv⟩
  push_cast
  constructor
  · intro h
    exact dvd_mul_of_dvd_right (dvd_trans (dvd_mul_left _ _) h) _
  · intro h
    rw [mul_comm]
    exact hqM.mul_dvd (hqv.dvd_of_dvd_mul_left h) hxM

theorem hdec_wElt (hq : q.Prime) (u v : ℤ) (huv : u * q + v * M = 1)
    (h1 : LevelLE M (M * q) (⊤ : Subgroup (ZMod M)ˣ) (⊤ : Subgroup (ZMod (M * q))ˣ) 1)
    (hq' : LevelLE M (M * q) (⊤ : Subgroup (ZMod M)ˣ) (⊤ : Subgroup (ZMod (M * q))ˣ) q)
    (g : ↥(GammaH M ⊤)) :
    (wElt u v huv)⁻¹ * g ∈ (iotaDeg M (M * q) ⊤ ⊤ q hq').range ∨
      ∃ l ∈ (iotaDeg M (M * q) ⊤ ⊤ 1 h1).range,
        l⁻¹ * g ∈ (iotaDeg M (M * q) ⊤ ⊤ q hq').range := by
  by_cases hd : (q : ℤ) ∣ (g : SL(2, ℤ)) 1 1
  · left
    rw [mem_range_iotaDeg_q_iff]
    show (q : ℤ) ∣ ((wMat (M := M) (q := q) u v huv)⁻¹ * (g : SL(2, ℤ)) : SL(2, ℤ)) 0 1
    rw [winv_g_01]
    exact dvd_add (dvd_mul_right _ _) (dvd_mul_of_dvd_right hd _)
  · right
    haveI : Fact q.Prime := ⟨hq⟩
    have hd0 : (((g : SL(2, ℤ)) 1 1 : ℤ) : ZMod q) ≠ 0 := by
      rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    let t : ℤ := ((((((g : SL(2, ℤ)) 0 1 : ℤ) : ZMod q) * (((g : SL(2, ℤ)) 1 1 : ℤ) : ZMod q)⁻¹).val
      : ℕ) : ℤ)
    refine ⟨uElt M ⊤ t, ?_, ?_⟩
    · rw [mem_range_iotaDeg_one_iff, coe_uElt, Gamma0_mem, uMat_apply_10, Int.cast_zero]
    · rw [mem_range_iotaDeg_q_iff]
      show (q : ℤ) ∣ ((uMat t)⁻¹ * (g : SL(2, ℤ)) : SL(2, ℤ)) 0 1
      rw [uinv_g_01, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      simp only [t, Int.cast_natCast, ZMod.natCast_zmod_val]
      rw [mul_assoc, ZMod.inv_mul_of_unit _ (IsUnit.mk0 (G₀ := ZMod q) _ hd0), mul_one, sub_self]

theorem hnot_wElt (hq : q.Prime) (u v : ℤ) (huv : u * q + v * M = 1)
    (h1 : LevelLE M (M * q) (⊤ : Subgroup (ZMod M)ˣ) (⊤ : Subgroup (ZMod (M * q))ˣ) 1)
    (hq' : LevelLE M (M * q) (⊤ : Subgroup (ZMod M)ˣ) (⊤ : Subgroup (ZMod (M * q))ˣ) q)
    (l : ↥(GammaH M ⊤)) (hl : l ∈ (iotaDeg M (M * q) ⊤ ⊤ 1 h1).range) :
    l⁻¹ * wElt u v huv ∉ (iotaDeg M (M * q) ⊤ ⊤ q hq').range := by
  intro hmem
  rw [mem_range_iotaDeg_q_iff] at hmem
  change (q : ℤ) ∣ ((l : SL(2, ℤ))⁻¹ * wMat (M := M) (q := q) u v huv : SL(2, ℤ)) 0 1 at hmem
  rw [linv_w_01, dvd_neg] at hmem
  have hdv : (q : ℤ) ∣ (l : SL(2, ℤ)) 1 1 * v := (dvd_add_left (dvd_mul_left _ _)).mp hmem
  have hqv : IsCoprime (q : ℤ) v := ⟨u, M, by linear_combination huv⟩
  have hd : (q : ℤ) ∣ (l : SL(2, ℤ)) 1 1 := hqv.dvd_of_dvd_mul_right hdv
  rw [mem_range_iotaDeg_one_iff, Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hl
  have hc : (q : ℤ) ∣ (l : SL(2, ℤ)) 1 0 := dvd_trans (by push_cast; exact dvd_mul_left _ _) hl
  have hdet := Matrix.SpecialLinearGroup.det_coe (l : SL(2, ℤ))
  rw [Matrix.det_fin_two] at hdet
  have h1' : (q : ℤ) ∣ 1 := by
    rw [← hdet]
    exact dvd_sub (dvd_mul_of_dvd_right hd _) (dvd_mul_of_dvd_right hc _)
  have := Int.eq_one_of_dvd_one (Int.natCast_nonneg q) h1'
  exact hq.one_lt.ne' (by exact_mod_cast this)

theorem hdec_same (hq : q.Prime) (u v : ℤ) (huv : u * q + v * M = 1)
    (h1 : LevelLE M (M * q) (⊤ : Subgroup (ZMod M)ˣ) (⊤ : Subgroup (ZMod (M * q))ˣ) 1)
    (hq' : LevelLE M (M * q) (⊤ : Subgroup (ZMod M)ˣ) (⊤ : Subgroup (ZMod (M * q))ˣ) q)
    (g : ↥(GammaH M ⊤)) :
    g ∈ (iotaDeg M (M * q) ⊤ ⊤ 1 h1).range ∨
      ∃ l ∈ (iotaDeg M (M * q) ⊤ ⊤ 1 h1).range,
        wElt u v huv * l⁻¹ * g ∈ (iotaDeg M (M * q) ⊤ ⊤ 1 h1).range := by
  rcases hdec_wElt hq u v huv h1 hq' (g * wElt u v huv) with h | ⟨l, hl, hlg⟩
  · left
    rw [hw_wElt u v huv h1 hq']
    rwa [← mul_assoc] at h
  · right
    refine ⟨l, hl, ?_⟩
    rw [hw_wElt u v huv h1 hq']
    have : (wElt u v huv)⁻¹ * (wElt u v huv * l⁻¹ * g) * wElt u v huv = l⁻¹ * (g * wElt u v huv) := by
      group
    rw [this]
    exact hlg

theorem hnot_same (hq : q.Prime) (u v : ℤ) (huv : u * q + v * M = 1)
    (h1 : LevelLE M (M * q) (⊤ : Subgroup (ZMod M)ˣ) (⊤ : Subgroup (ZMod (M * q))ˣ) 1)
    (hq' : LevelLE M (M * q) (⊤ : Subgroup (ZMod M)ˣ) (⊤ : Subgroup (ZMod (M * q))ˣ) q) :
    wElt u v huv ∉ (iotaDeg M (M * q) ⊤ ⊤ 1 h1).range := by
  intro hw
  have h := hnot_wElt hq u v huv h1 hq' (wElt u v huv) hw
  rw [inv_mul_cancel] at h
  exact h (one_mem _)

section AL

variable (u v : ℤ) (huv : u * q + v * M = 1)
  (h1 : LevelLE M (M * q) (⊤ : Subgroup (ZMod M)ˣ) (⊤ : Subgroup (ZMod (M * q))ˣ) 1)
  (hq' : LevelLE M (M * q) (⊤ : Subgroup (ZMod M)ˣ) (⊤ : Subgroup (ZMod (M * q))ˣ) q)

def eHat : ↥(GammaH M ⊤) ≃* ↥(GammaH M ⊤) := MulAut.conj (wElt u v huv)⁻¹

theorem eHat_apply (x : ↥(GammaH M ⊤)) :
    eHat u v huv x = (wElt u v huv)⁻¹ * x * wElt u v huv := by
  simp [eHat]

theorem mem_range_one_iff_eHat_mem_range_q (x : ↥(GammaH M ⊤)) :
    x ∈ (iotaDeg M (M * q) ⊤ ⊤ 1 h1).range ↔ eHat u v huv x ∈ (iotaDeg M (M * q) ⊤ ⊤ q hq').range := by
  rw [eHat_apply]; exact hw_wElt u v huv h1 hq' x

noncomputable def eOne : ↥(GammaH (M * q) ⊤) ≃* ↥((iotaDeg M (M * q) ⊤ ⊤ 1 h1).range) :=
  MonoidHom.ofInjective (iotaDeg_injective M (M * q) ⊤ ⊤ 1 h1)

noncomputable def eQ : ↥(GammaH (M * q) ⊤) ≃* ↥((iotaDeg M (M * q) ⊤ ⊤ q hq').range) :=
  MonoidHom.ofInjective (iotaDeg_injective M (M * q) ⊤ ⊤ q hq')

theorem coe_eOne (γ : ↥(GammaH (M * q) ⊤)) :
    ((eOne h1 γ : ↥((iotaDeg M (M * q) ⊤ ⊤ 1 h1).range)) : ↥(GammaH M ⊤)) =
      iotaDeg M (M * q) ⊤ ⊤ 1 h1 γ := rfl

theorem coe_eQ (γ : ↥(GammaH (M * q) ⊤)) :
    ((eQ hq' γ : ↥((iotaDeg M (M * q) ⊤ ⊤ q hq').range)) : ↥(GammaH M ⊤)) =
      iotaDeg M (M * q) ⊤ ⊤ q hq' γ := rfl

theorem iotaDeg_eQ_symm (y : ↥((iotaDeg M (M * q) ⊤ ⊤ q hq').range)) :
    iotaDeg M (M * q) ⊤ ⊤ q hq' ((eQ hq').symm y) = y :=
  MonoidHom.apply_ofInjective_symm (iotaDeg_injective M (M * q) ⊤ ⊤ q hq') y

theorem iotaDeg_eOne_symm (y : ↥((iotaDeg M (M * q) ⊤ ⊤ 1 h1).range)) :
    iotaDeg M (M * q) ⊤ ⊤ 1 h1 ((eOne h1).symm y) = y :=
  MonoidHom.apply_ofInjective_symm (iotaDeg_injective M (M * q) ⊤ ⊤ 1 h1) y

noncomputable def toRangeQ :
    ↥((iotaDeg M (M * q) ⊤ ⊤ 1 h1).range) →* ↥((iotaDeg M (M * q) ⊤ ⊤ q hq').range) :=
  ((eHat u v huv).toMonoidHom.comp (iotaDeg M (M * q) ⊤ ⊤ 1 h1).range.subtype).codRestrict _
    (fun x => (mem_range_one_iff_eHat_mem_range_q u v huv h1 hq' x).mp x.2)

@[scoped simp] theorem coe_toRangeQ (x : ↥((iotaDeg M (M * q) ⊤ ⊤ 1 h1).range)) :
    ((toRangeQ u v huv h1 hq' x : ↥((iotaDeg M (M * q) ⊤ ⊤ q hq').range)) : ↥(GammaH M ⊤)) =
      eHat u v huv x := rfl

noncomputable def cW : ↥(GammaH (M * q) ⊤) →* ↥(GammaH (M * q) ⊤) :=
  (eQ hq').symm.toMonoidHom.comp ((toRangeQ u v huv h1 hq').comp (eOne h1).toMonoidHom)

theorem iotaDeg_q_cW (γ : ↥(GammaH (M * q) ⊤)) :
    iotaDeg M (M * q) ⊤ ⊤ q hq' (cW u v huv h1 hq' γ) = eHat u v huv (iotaDeg M (M * q) ⊤ ⊤ 1 h1 γ) := by
  show iotaDeg M (M * q) ⊤ ⊤ q hq' ((eQ hq').symm (toRangeQ u v huv h1 hq' (eOne h1 γ))) = _
  rw [iotaDeg_eQ_symm, coe_toRangeQ, coe_eOne]

include hq' in

theorem mem_GammaHUpper_iff_eOne_mem_stabSub (γ : ↥(GammaH (M * q) ⊤)) :
    γ ∈ GammaHUpper (M * q) ⊤ q ↔
      eOne h1 γ ∈ stabSub (iotaDeg M (M * q) ⊤ ⊤ 1 h1).range (wElt u v huv) := by
  rw [mem_stabSub_iff, coe_eOne, hw_wElt u v huv h1 hq', mem_range_iotaDeg_q_iff]
  have : (wElt u v huv)⁻¹ * (wElt u v huv * iotaDeg M (M * q) ⊤ ⊤ 1 h1 γ * (wElt u v huv)⁻¹) *
      wElt u v huv = iotaDeg M (M * q) ⊤ ⊤ 1 h1 γ := by group
  rw [this, coe_iotaDeg_one h1, Subgroup.mem_subgroupOf, mem_Gamma0Upper,
    ZMod.intCast_zmod_eq_zero_iff_dvd]

include hq' in
theorem stabSub_finiteIndex :
    (stabSub (iotaDeg M (M * q) ⊤ ⊤ 1 h1).range (wElt u v huv)).FiniteIndex := by
  refine ⟨fun h0 => ?_⟩
  have hidx := index_eq_of_equiv (eOne h1) (GammaHUpper (M * q) ⊤ q)
    (stabSub (iotaDeg M (M * q) ⊤ ⊤ 1 h1).range (wElt u v huv))
    (mem_GammaHUpper_iff_eOne_mem_stabSub u v huv h1 hq')
  rw [← hidx] at h0
  exact Subgroup.FiniteIndex.index_ne_zero h0

variable {A : Type} [AddCommGroup A]

noncomputable def P (φ : H1 (M * q) ⊤ A) : H1 (M * q) ⊤ A :=
  φ.comp (MonoidHom.toAdditive (cW u v huv h1 hq'))

theorem P_apply (φ : H1 (M * q) ⊤ A) (γ : ↥(GammaH (M * q) ⊤)) :
    P u v huv h1 hq' φ (Additive.ofMul γ) = φ (Additive.ofMul (cW u v huv h1 hq' γ)) := rfl

theorem P_add (φ ψ : H1 (M * q) ⊤ A) : P u v huv h1 hq' (φ + ψ) = P u v huv h1 hq' φ + P u v huv h1 hq' ψ := by
  ext; rfl

theorem P_neg (φ : H1 (M * q) ⊤ A) : P u v huv h1 hq' (-φ) = -P u v huv h1 hq' φ := by
  ext; rfl

theorem P_zero : P u v huv h1 hq' (0 : H1 (M * q) ⊤ A) = 0 := by
  ext; rfl

theorem char_conjL_eq (φ : H1 (M * q) ⊤ A) :
    (AddMonoidHom.toMultiplicativeRight φ).comp (conjL (M * q) ⊤ q) =
      ((AddMonoidHom.toMultiplicativeRight
          (pushChar M (M * q) ⊤ ⊤ 1 A h1 (P u v huv h1 hq' φ))).comp
        (conjIn (iotaDeg M (M * q) ⊤ ⊤ 1 h1).range (wElt u v huv))).comp
      (restrictEquiv (eOne h1) (GammaHUpper (M * q) ⊤ q)
        (stabSub (iotaDeg M (M * q) ⊤ ⊤ 1 h1).range (wElt u v huv))
        (mem_GammaHUpper_iff_eOne_mem_stabSub u v huv h1 hq')) := by
  ext k
  simp only [MonoidHom.comp_apply, AddMonoidHom.toMultiplicativeRight_apply_apply]

  show Multiplicative.ofAdd (φ (Additive.ofMul (conjL (M * q) ⊤ q k))) =
    Multiplicative.ofAdd ((P u v huv h1 hq' φ) (Additive.ofMul ((eOne h1).symm
      (conjIn (iotaDeg M (M * q) ⊤ ⊤ 1 h1).range (wElt u v huv)
        (restrictEquiv (eOne h1) (GammaHUpper (M * q) ⊤ q)
          (stabSub (iotaDeg M (M * q) ⊤ ⊤ 1 h1).range (wElt u v huv))
          (mem_GammaHUpper_iff_eOne_mem_stabSub u v huv h1 hq') k)))))
  rw [P_apply]
  congr 3
  apply iotaDeg_injective M (M * q) ⊤ ⊤ q hq'
  rw [iotaDeg_q_conjL h1 hq', iotaDeg_q_cW, iotaDeg_eOne_symm, eHat_apply]
  apply Subtype.ext
  simp only [coe_conjIn, coe_restrictEquiv, Subgroup.coe_mul, Subgroup.coe_inv, coe_eOne]
  group

theorem jDeg_one_P (φ : H1 (M * q) ⊤ A) :
    jDeg M (M * q) ⊤ ⊤ 1 A h1 (P u v huv h1 hq' φ) = jDeg M (M * q) ⊤ ⊤ q A hq' φ := by

  set χq : ↥((iotaDeg M (M * q) ⊤ ⊤ q hq').range) →* Multiplicative A :=
    AddMonoidHom.toMultiplicativeRight (pushChar M (M * q) ⊤ ⊤ q A hq' φ) with hχq
  have hchar : AddMonoidHom.toMultiplicativeRight (pushChar M (M * q) ⊤ ⊤ 1 A h1 (P u v huv h1 hq' φ))
      = χq.comp (restrictEquiv (eHat u v huv) _ _
          (mem_range_one_iff_eHat_mem_range_q u v huv h1 hq')) := by
    ext y
    simp only [MonoidHom.comp_apply, AddMonoidHom.toMultiplicativeRight_apply_apply, hχq]
    show Multiplicative.ofAdd ((P u v huv h1 hq' φ) (Additive.ofMul ((eOne h1).symm y))) =
      Multiplicative.ofAdd (φ (Additive.ofMul ((eQ hq').symm
        (restrictEquiv (eHat u v huv) _ _ (mem_range_one_iff_eHat_mem_range_q u v huv h1 hq') y))))
    rw [P_apply]
    congr 3
    show (eQ hq').symm (toRangeQ u v huv h1 hq' (eOne h1 ((eOne h1).symm y))) = _
    rw [MulEquiv.apply_symm_apply]
    congr 1
  ext x
  show Multiplicative.toAdd (MonoidHom.transfer
      (AddMonoidHom.toMultiplicativeRight (pushChar M (M * q) ⊤ ⊤ 1 A h1 (P u v huv h1 hq' φ)))
      (Additive.toMul x)) =
    Multiplicative.toAdd (MonoidHom.transfer χq (Additive.toMul x))
  have e1 : MonoidHom.transfer χq ((wElt u v huv)⁻¹ * Additive.toMul x * wElt u v huv) =
      MonoidHom.transfer χq (Additive.toMul x) := by
    rw [MonoidHom.map_mul, MonoidHom.map_mul, MonoidHom.map_inv, inv_mul_cancel_comm]
  rw [hchar, transfer_comp_equiv, eHat_apply, e1]

theorem heckeT_apply_ofMul (φ : H1 (M * q) ⊤ A) (γ : ↥(GammaH (M * q) ⊤)) :
    heckeT (M * q) ⊤ q A φ (Additive.ofMul γ) =
      Multiplicative.toAdd (MonoidHom.transfer
        ((AddMonoidHom.toMultiplicativeRight φ).comp (conjL (M * q) ⊤ q)) γ) := rfl

theorem heckeT_apply_eq (hq : q.Prime) (φ : H1 (M * q) ⊤ A) (γ : ↥(GammaH (M * q) ⊤)) :
    heckeT (M * q) ⊤ q A φ (Additive.ofMul γ) =
      jDeg M (M * q) ⊤ ⊤ 1 A h1 (P u v huv h1 hq' φ) (Additive.ofMul (iotaDeg M (M * q) ⊤ ⊤ 1 h1 γ))
        - P u v huv h1 hq' φ (Additive.ofMul γ) := by
  set H : Subgroup ↥(GammaH M ⊤) := (iotaDeg M (M * q) ⊤ ⊤ 1 h1).range
  set χ₁ : ↥H →* Multiplicative A :=
    AddMonoidHom.toMultiplicativeRight (pushChar M (M * q) ⊤ ⊤ 1 A h1 (P u v huv h1 hq' φ)) with hχ₁
  haveI := stabSub_finiteIndex u v huv h1 hq'
  have hM := transfer_mackey_same H (wElt u v huv) (hdec_same hq u v huv h1 hq')
    (hnot_same hq u v huv h1 hq') χ₁ (eOne h1 γ)
  have hnat := transfer_comp_equiv (eOne h1) (GammaHUpper (M * q) ⊤ q) (stabSub H (wElt u v huv))
    (mem_GammaHUpper_iff_eOne_mem_stabSub u v huv h1 hq') (χ₁.comp (conjIn H (wElt u v huv))) γ
  rw [heckeT_apply_ofMul, char_conjL_eq u v huv h1 hq' φ, hnat, eq_inv_mul_of_mul_eq hM.symm,
    toAdd_mul, toAdd_inv]

  have hj : Multiplicative.toAdd (MonoidHom.transfer χ₁ ((eOne h1 γ : ↥H) : ↥(GammaH M ⊤))) =
      jDeg M (M * q) ⊤ ⊤ 1 A h1 (P u v huv h1 hq' φ)
        (Additive.ofMul (iotaDeg M (M * q) ⊤ ⊤ 1 h1 γ)) := rfl
  have hP : Multiplicative.toAdd (χ₁ (eOne h1 γ)) = P u v huv h1 hq' φ (Additive.ofMul γ) := by
    show (pushChar M (M * q) ⊤ ⊤ 1 A h1 (P u v huv h1 hq' φ)) (Additive.ofMul (eOne h1 γ)) = _
    show (P u v huv h1 hq' φ) (Additive.ofMul ((eOne h1).symm (eOne h1 γ))) = _
    rw [MulEquiv.symm_apply_apply]
  rw [hj, hP]
  abel

theorem mulq {R : Type*} [CommRing R] (X Y : Matrix (Fin 2) (Fin 2) R) (i j : Fin 2) :
    (X * Y) i j = X i 0 * Y 0 j + X i 1 * Y 1 j := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]

def Mq : Matrix (Fin 2) (Fin 2) ℤ →+* Matrix (Fin 2) (Fin 2) ℚ := (Int.castRingHom ℚ).mapMatrix

theorem Mq_apply (X : Matrix (Fin 2) (Fin 2) ℤ) (i j : Fin 2) : Mq X i j = (X i j : ℚ) := rfl

theorem Mq_injective : Function.Injective Mq := by
  intro X Y h
  funext i j
  have := congrFun (congrFun h i) j
  rw [Mq_apply, Mq_apply] at this
  exact_mod_cast this

def δ (n : ℕ) : Matrix (Fin 2) (Fin 2) ℚ := !![(n : ℚ), 0; 0, 1]
def δ' (n : ℕ) : Matrix (Fin 2) (Fin 2) ℚ := !![(n : ℚ)⁻¹, 0; 0, 1]

@[scoped simp] theorem δ_00 (n : ℕ) : δ n 0 0 = n := rfl
@[scoped simp] theorem δ_01 (n : ℕ) : δ n 0 1 = 0 := rfl
@[scoped simp] theorem δ_10 (n : ℕ) : δ n 1 0 = 0 := rfl
@[scoped simp] theorem δ_11 (n : ℕ) : δ n 1 1 = 1 := rfl
@[scoped simp] theorem δ'_00 (n : ℕ) : δ' n 0 0 = (n : ℚ)⁻¹ := rfl
@[scoped simp] theorem δ'_01 (n : ℕ) : δ' n 0 1 = 0 := rfl
@[scoped simp] theorem δ'_10 (n : ℕ) : δ' n 1 0 = 0 := rfl
@[scoped simp] theorem δ'_11 (n : ℕ) : δ' n 1 1 = 1 := rfl

theorem δ'_mul_δ : δ' q * δ q = 1 := by
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne q
  funext i j
  fin_cases i <;> fin_cases j <;> simp [mulq, hq0]

theorem Mq_conjLowerMat (z : SL(2, ℤ)) (hz : (q : ℤ) ∣ z 1 0) :
    Mq (conjLowerMat q z hz : SL(2, ℤ)) = δ q * Mq (z : Matrix (Fin 2) (Fin 2) ℤ) * δ' q := by
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hq0' : ((q : ℤ) : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne q
  funext i j
  fin_cases i <;> fin_cases j <;> simp [mulq, Mq_apply]
  · rw [mul_comm (q : ℚ), mul_inv_cancel_right₀ hq0]
  · exact mul_comm _ _
  · rw [Int.cast_div hz hq0', div_eq_mul_inv, Int.cast_natCast]

def Wi : Matrix (Fin 2) (Fin 2) ℚ := δ' q * Mq ((wMat (M := M) (q := q) u v huv)⁻¹ : SL(2, ℤ))
def Wm : Matrix (Fin 2) (Fin 2) ℚ := Mq (wMat (M := M) (q := q) u v huv : SL(2, ℤ)) * δ q

theorem Mq_cW (γ : ↥(GammaH (M * q) ⊤)) :
    Mq ((cW u v huv h1 hq' γ : ↥(GammaH (M * q) ⊤)) : SL(2, ℤ)) =
      Wi u v huv * Mq ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * Wm u v huv := by
  have key := congrArg (fun x : ↥(GammaH M ⊤) => Mq ((x : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ))
    (iotaDeg_q_cW u v huv h1 hq' γ)
  have hL : ((iotaDeg M (M * q) ⊤ ⊤ q hq' (cW u v huv h1 hq' γ) : ↥(GammaH M ⊤)) : SL(2, ℤ)) =
      conjLowerMat q ((cW u v huv h1 hq' γ : ↥(GammaH (M * q) ⊤)) : SL(2, ℤ))
        (hq'.dvd_entry (cW u v huv h1 hq' γ)) := rfl
  have hR : ((eHat u v huv (iotaDeg M (M * q) ⊤ ⊤ 1 h1 γ) : ↥(GammaH M ⊤)) : SL(2, ℤ)) =
      (wMat (M := M) (q := q) u v huv)⁻¹ * (γ : SL(2, ℤ)) * wMat (M := M) (q := q) u v huv := by
    rw [eHat_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_iotaDeg_one h1]
    rfl
  rw [hL, hR, Mq_conjLowerMat, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    map_mul, map_mul] at key

  set X := Mq ((cW u v huv h1 hq' γ : ↥(GammaH (M * q) ⊤)) : SL(2, ℤ)) with hX
  have : X = δ' q * (δ q * X * δ' q) * δ q := by
    rw [show δ' q * (δ q * X * δ' q) * δ q = (δ' q * δ q) * X * (δ' q * δ q) by
      simp only [mul_assoc], δ'_mul_δ, one_mul, mul_one]
  rw [this, key]
  unfold Wi Wm
  simp only [mul_assoc]

def mMat : SL(2, ℤ) :=
  ⟨!![(q : ℤ) * u ^ 2 - v * M, -(u * v) - v; (M : ℤ) * u * q + M * q, -((M : ℤ) * v) + q], by
    rw [Matrix.det_fin_two_of]
    linear_combination (u * q + v * M + 1) * huv⟩

@[scoped simp] theorem mMat_00 : (mMat (M := M) (q := q) u v huv) 0 0 = (q : ℤ) * u ^ 2 - v * M := rfl
@[scoped simp] theorem mMat_01 : (mMat (M := M) (q := q) u v huv) 0 1 = -(u * v) - v := rfl
@[scoped simp] theorem mMat_10 : (mMat (M := M) (q := q) u v huv) 1 0 = (M : ℤ) * u * q + M * q := rfl
@[scoped simp] theorem mMat_11 : (mMat (M := M) (q := q) u v huv) 1 1 = -((M : ℤ) * v) + q := rfl

theorem mMat_mem : mMat (M := M) (q := q) u v huv ∈ GammaH (M * q) ⊤ := by
  rw [GammaH_top, Gamma0_mem, mMat_10, ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact ⟨u + 1, by push_cast; ring⟩

def mElt : ↥(GammaH (M * q) ⊤) := ⟨mMat u v huv, mMat_mem u v huv⟩

theorem Wm_mul_Wm : Wm u v huv * Wm u v huv = (q : ℚ) • Mq (mMat (M := M) (q := q) u v huv : SL(2, ℤ)) := by
  funext i j
  fin_cases i <;> fin_cases j <;> simp [Wm, mulq, Mq_apply, Matrix.smul_apply] <;> ring

theorem Wi_mul_Wi : Wi u v huv * Wi u v huv =
    (q : ℚ)⁻¹ • Mq ((mMat (M := M) (q := q) u v huv)⁻¹ : SL(2, ℤ)) := by
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne q
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [Wi, mulq, Mq_apply, Matrix.smul_apply, Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two] <;> field_simp <;> ring

theorem cW_cW (γ : ↥(GammaH (M * q) ⊤)) :
    cW u v huv h1 hq' (cW u v huv h1 hq' γ) = (mElt u v huv)⁻¹ * γ * mElt u v huv := by
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne q
  apply Subtype.ext
  apply Subtype.ext
  apply Mq_injective
  show Mq ((cW u v huv h1 hq' (cW u v huv h1 hq' γ) : ↥(GammaH (M * q) ⊤)) : SL(2, ℤ)) =
    Mq ((((mElt u v huv)⁻¹ * γ * mElt u v huv : ↥(GammaH (M * q) ⊤)) : SL(2, ℤ)) : Matrix _ _ ℤ)
  rw [Mq_cW, Mq_cW]
  have : Wi u v huv * (Wi u v huv * Mq ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * Wm u v huv) *
      Wm u v huv = (Wi u v huv * Wi u v huv) * Mq ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
        (Wm u v huv * Wm u v huv) := by
    simp only [mul_assoc]
  rw [this, Wi_mul_Wi, Wm_mul_Wm, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul,
    inv_mul_cancel₀ hq0, one_smul]
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, map_mul, map_mul]
  rfl

theorem P_P (φ : H1 (M * q) ⊤ A) : P u v huv h1 hq' (P u v huv h1 hq' φ) = φ := by
  ext x
  show φ (Additive.ofMul (cW u v huv h1 hq' (cW u v huv h1 hq' (Additive.toMul x)))) = φ x
  rw [cW_cW, ofMul_mul, ofMul_mul, ofMul_inv, map_add, map_add, map_neg]
  show -φ (Additive.ofMul (mElt u v huv)) + φ x + φ (Additive.ofMul (mElt u v huv)) = φ x
  abel

end AL

end Concrete

section Assembly

open CohCarrier CongruenceSubgroup
open scoped MatrixGroups

theorem main (N r : ℕ) [NeZero N] [NeZero r] (hr : r.Prime) (hrN : ¬ r ∣ N)
    (A : Type) [AddCommGroup A]
    (h₁ : LevelLE N (N * r) ⊤ ⊤ 1) (hr' : LevelLE N (N * r) ⊤ ⊤ r)
    (φ : H1 (N * r) ⊤ A)
    (hφ₁ : jDeg N (N * r) ⊤ ⊤ 1 A h₁ φ = 0)
    (hφr : jDeg N (N * r) ⊤ ⊤ r A hr' φ = 0) :
    heckeT (N * r) ⊤ r A (heckeT (N * r) ⊤ r A φ) = φ := by

  have hcop : Nat.Coprime r N := (Nat.Prime.coprime_iff_not_dvd hr).mpr hrN
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop

  have hII : ∀ ψ : H1 (N * r) ⊤ A,
      jDeg N (N * r) ⊤ ⊤ 1 A h₁ (P u v huv h₁ hr' ψ) = jDeg N (N * r) ⊤ ⊤ r A hr' ψ :=
    fun ψ => jDeg_one_P u v huv h₁ hr' ψ
  have hPP : ∀ ψ : H1 (N * r) ⊤ A, P u v huv h₁ hr' (P u v huv h₁ hr' ψ) = ψ :=
    fun ψ => P_P u v huv h₁ hr' ψ
  have hII' : ∀ ψ : H1 (N * r) ⊤ A,
      jDeg N (N * r) ⊤ ⊤ r A hr' (P u v huv h₁ hr' ψ) = jDeg N (N * r) ⊤ ⊤ 1 A h₁ ψ := by
    intro ψ
    rw [← hII (P u v huv h₁ hr' ψ), hPP]

  have hU : ∀ ψ : H1 (N * r) ⊤ A, jDeg N (N * r) ⊤ ⊤ r A hr' ψ = 0 →
      heckeT (N * r) ⊤ r A ψ = -P u v huv h₁ hr' ψ := by
    intro ψ hψ
    refine AddMonoidHom.ext fun x => ?_
    rw [← ofMul_toMul x, heckeT_apply_eq u v huv h₁ hr' hr ψ (Additive.toMul x), hII, hψ,
      AddMonoidHom.zero_apply, zero_sub, AddMonoidHom.neg_apply]

  have hPφ : jDeg N (N * r) ⊤ ⊤ r A hr' (P u v huv h₁ hr' φ) = 0 := by rw [hII', hφ₁]
  rw [hU φ hφr, map_neg, hU _ hPφ, neg_neg, hPP]

end Assembly

end ALInvolSol
p2m_reactivate "P2MW.S_CohCarrier_heckeT_heckeT_eq_self_of_jDeg_one_eq_zero_of_jDeg_eq_zero.ALInvolSol"

open CohCarrier in

theorem solution
    (N r : ℕ) [NeZero N] [NeZero r] (hr : r.Prime) (hrN : ¬ r ∣ N)
    (A : Type) [AddCommGroup A]

    (h₁ : CohCarrier.LevelLE N (N * r) ⊤ ⊤ 1) (hr' : CohCarrier.LevelLE N (N * r) ⊤ ⊤ r)

    (φ : CohCarrier.H1 (N * r) ⊤ A)
    (hφ₁ : CohCarrier.jDeg N (N * r) ⊤ ⊤ 1 A h₁ φ = 0)
    (hφr : CohCarrier.jDeg N (N * r) ⊤ ⊤ r A hr' φ = 0) :
    CohCarrier.heckeT (N * r) ⊤ r A (CohCarrier.heckeT (N * r) ⊤ r A φ) = φ :=
  ALInvolSol.main N r hr hrN A h₁ hr' φ hφ₁ hφr

end S_CohCarrier_heckeT_heckeT_eq_self_of_jDeg_one_eq_zero_of_jDeg_eq_zero
end P2MW
export P2MW.S_CohCarrier_heckeT_heckeT_eq_self_of_jDeg_one_eq_zero_of_jDeg_eq_zero (solution)
