-- Prove2me | solution 1 for CohCarrier.heckeT_heckeTlower_eq_add_smul_iDeg_jDeg_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/a1c6572f-9e79-59cb-9679-eb75cdfb4cee

import Mathlib
import Definitions.Def_CohCarrier_Lower
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_heckeT_heckeTlower_eq_add_smul_iDeg_jDeg_of_prime

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace IwahoriQuadSol

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

theorem transfer_restrict_eq_pow [H.FiniteIndex] (φ : G →* C) (g : G) :
    MonoidHom.transfer (φ.domRestrict H) g = φ g ^ H.index := by
  rw [transfer_eq_prod_section (φ.domRestrict H) Quotient.out Quotient.out_eq g]
  simp only [MonoidHom.domRestrict_apply, map_mul, map_inv]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_inv_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.prod_equiv (MulAction.toPerm g⁻¹ : Equiv.Perm (G ⧸ H))
      (fun q : G ⧸ H => φ (Quotient.out (g⁻¹ • q))) (fun q : G ⧸ H => φ (Quotient.out q))
      (fun _ => rfl),
    H.index_eq_card, Nat.card_eq_fintype_card, mul_comm (φ g ^ _), ← mul_assoc, inv_mul_cancel,
    one_mul]

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

def inclSubgroupOf (Γ Γ'' : Subgroup G) : ↥(Γ''.subgroupOf Γ) →* ↥Γ'' :=
  (Γ.subtype.domRestrict (Γ''.subgroupOf Γ)).codRestrict Γ''
    (fun y => Subgroup.mem_subgroupOf.mp y.2)

@[scoped simp] theorem coe_inclSubgroupOf (Γ Γ'' : Subgroup G) (y : ↥(Γ''.subgroupOf Γ)) :
    (inclSubgroupOf Γ Γ'' y : G) = ((y : Γ) : G) := rfl

def optMap (Γ Γ'' : Subgroup G) (w : G) : Option (Γ ⧸ Γ''.subgroupOf Γ) → G ⧸ Γ'' :=
  fun o => o.elim (QuotientGroup.mk w)
    (Quotient.map' (fun x : Γ => (x : G)) (fun x y hxy => by
      rw [QuotientGroup.leftRel_apply] at hxy ⊢
      exact Subgroup.mem_subgroupOf.mp hxy))

theorem optMap_none (Γ Γ'' : Subgroup G) (w : G) :
    optMap Γ Γ'' w none = QuotientGroup.mk w := rfl

theorem optMap_some_mk (Γ Γ'' : Subgroup G) (w : G) (x : Γ) :
    optMap Γ Γ'' w (some (QuotientGroup.mk x)) = QuotientGroup.mk (x : G) := rfl

theorem optMap_some_smul (Γ Γ'' : Subgroup G) (w : G) (y : Γ) (p : Γ ⧸ Γ''.subgroupOf Γ) :
    optMap Γ Γ'' w (some (y • p)) = (y : G) • optMap Γ Γ'' w (some p) := by
  induction p using Quotient.inductionOn' with | h a => ?_
  change optMap Γ Γ'' w (some (y • QuotientGroup.mk a)) = (y : G) • optMap Γ Γ'' w (some (QuotientGroup.mk a))
  rw [MulAction.Quotient.smul_mk, optMap_some_mk, optMap_some_mk, MulAction.Quotient.smul_mk,
    smul_eq_mul, smul_eq_mul, Subgroup.coe_mul]

theorem optMap_bijective (Γ Γ'' : Subgroup G) (w : G)
    (hdec : ∀ g : G, w⁻¹ * g ∈ Γ'' ∨ ∃ l ∈ Γ, l⁻¹ * g ∈ Γ'')
    (hnot : ∀ l ∈ Γ, l⁻¹ * w ∉ Γ'') :
    Function.Bijective (optMap Γ Γ'' w) := by
  constructor
  · rintro (_ | a) (_ | b) hab
    · rfl
    · exfalso
      induction b using Quotient.inductionOn' with | h b => ?_
      change (QuotientGroup.mk w : G ⧸ Γ'') = QuotientGroup.mk (b : G) at hab
      rw [eq_comm, QuotientGroup.eq] at hab
      exact hnot b b.2 hab
    · exfalso
      induction a using Quotient.inductionOn' with | h a => ?_
      change QuotientGroup.mk (a : G) = (QuotientGroup.mk w : G ⧸ Γ'') at hab
      rw [QuotientGroup.eq] at hab
      exact hnot a a.2 hab
    · induction a using Quotient.inductionOn' with | h a => ?_
      induction b using Quotient.inductionOn' with | h b => ?_
      change QuotientGroup.mk (a : G) = (QuotientGroup.mk (b : G) : G ⧸ Γ'') at hab
      rw [QuotientGroup.eq] at hab
      change some (QuotientGroup.mk a : Γ ⧸ Γ''.subgroupOf Γ) = some (QuotientGroup.mk b)
      rw [Option.some_inj, QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul,
        Subgroup.coe_inv]
      exact hab
  · intro Q
    induction Q using Quotient.inductionOn' with | h g => ?_
    rcases hdec g with hg | ⟨l, hl, hlg⟩
    · exact ⟨none, by
        change (QuotientGroup.mk w : G ⧸ Γ'') = QuotientGroup.mk g
        rw [QuotientGroup.eq]; exact hg⟩
    · exact ⟨some (QuotientGroup.mk ⟨l, hl⟩), by
        change (QuotientGroup.mk l : G ⧸ Γ'') = QuotientGroup.mk g
        rw [QuotientGroup.eq]; exact hlg⟩

theorem index_eq_index_subgroupOf_add_one (Γ Γ'' : Subgroup G) [Γ''.FiniteIndex] (w : G)
    (hdec : ∀ g : G, w⁻¹ * g ∈ Γ'' ∨ ∃ l ∈ Γ, l⁻¹ * g ∈ Γ'')
    (hnot : ∀ l ∈ Γ, l⁻¹ * w ∉ Γ'') :
    Γ''.index = (Γ''.subgroupOf Γ).index + 1 := by
  rw [Subgroup.index_eq_card, Subgroup.index_eq_card,
    ← Nat.card_congr (Equiv.ofBijective _ (optMap_bijective Γ Γ'' w hdec hnot)),
    Finite.card_option]

theorem transfer_mackey_two (Γ Γ'' : Subgroup G) [Γ''.FiniteIndex]
    [(Γ''.subgroupOf Γ).FiniteIndex] (w : G)
    (hw : ∀ x ∈ Γ, w⁻¹ * x * w ∈ Γ'')
    (hdec : ∀ g : G, w⁻¹ * g ∈ Γ'' ∨ ∃ l ∈ Γ, l⁻¹ * g ∈ Γ'')
    (hnot : ∀ l ∈ Γ, l⁻¹ * w ∉ Γ'')
    (ψ : Γ'' →* C) (x : Γ) :
    MonoidHom.transfer ψ (x : G)
      = MonoidHom.transfer (ψ.comp (inclSubgroupOf Γ Γ'')) x * ψ ⟨w⁻¹ * x * w, hw x x.2⟩ := by
  set E : Option (Γ ⧸ Γ''.subgroupOf Γ) ≃ G ⧸ Γ'' :=
    Equiv.ofBijective (optMap Γ Γ'' w) (optMap_bijective Γ Γ'' w hdec hnot) with hE
  have hEa : ∀ o, E o = optMap Γ Γ'' w o := fun o => rfl

  let s : Γ ⧸ Γ''.subgroupOf Γ → Γ := Quotient.out
  have hs : ∀ p, (s p : Γ ⧸ Γ''.subgroupOf Γ) = p := fun p => Quotient.out_eq p
  let f : G ⧸ Γ'' → G := fun Q => (E.symm Q).elim w (fun p => (s p : G))
  have hf : ∀ Q, (f Q : G ⧸ Γ'') = Q := by
    intro Q
    obtain ⟨o, rfl⟩ := E.surjective Q
    simp only [f, Equiv.symm_apply_apply]
    cases o with
    | none => rfl
    | some p =>
        change QuotientGroup.mk (s p : G) = E (some p)
        rw [hEa]
        conv_rhs => rw [← hs p]
        rfl
  rw [transfer_eq_prod_section ψ f hf, transfer_eq_prod_section _ s hs,
    ← Fintype.prod_equiv E _ _ (fun _ => rfl), Fintype.prod_option, mul_comm]
  congr 1
  · refine Finset.prod_congr rfl (fun p _ => ?_)
    rw [MonoidHom.comp_apply]
    refine congrArg ψ (Subtype.ext ?_)
    have h1 : (x : G)⁻¹ • E (some p) = E (some (x⁻¹ • p)) := by
      rw [hEa, hEa, optMap_some_smul, Subgroup.coe_inv]
    simp only [coe_inclSubgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, f, h1,
      Equiv.symm_apply_apply, Option.elim]
  · refine congrArg ψ (Subtype.ext ?_)
    have h1 : (x : G)⁻¹ • E none = E none := by
      rw [hEa, optMap_none, MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq, mul_inv_rev,
        inv_inv]
      exact hw x x.2
    simp only [f, h1, Equiv.symm_apply_apply, Option.elim, mul_assoc]

end Mackey

section OneGroup

variable {G : Type*} [Group G] {C : Type*} [CommGroup C]

theorem transfer_mul' {H : Subgroup G} [H.FiniteIndex] (ϕ ψ : H →* C) :
    MonoidHom.transfer (ϕ * ψ) = MonoidHom.transfer ϕ * MonoidHom.transfer ψ := by
  ext g
  simp only [MonoidHom.mul_apply, MonoidHom.transfer_def _ default, Subgroup.leftTransversals.diff,
    Finset.prod_mul_distrib]

theorem transfer_inv' {H : Subgroup G} [H.FiniteIndex] (ψ : H →* C) :
    MonoidHom.transfer ψ⁻¹ = (MonoidHom.transfer ψ)⁻¹ := by
  ext g
  simp only [MonoidHom.inv_apply, MonoidHom.transfer_def _ default, Subgroup.leftTransversals.diff,
    Finset.prod_inv_distrib]

theorem transfer_comp_conj (Γ Γ'' : Subgroup G) [Γ.FiniteIndex] [Γ''.FiniteIndex] (w : G)
    (hw'' : ∀ y, y ∈ Γ'' ↔ (MulAut.conj w) y ∈ Γ) (φ : Γ →* C) (g : G) :
    MonoidHom.transfer (φ.comp (restrictEquiv (MulAut.conj w) Γ'' Γ hw'')) g
      = MonoidHom.transfer φ g := by
  rw [transfer_comp_equiv (MulAut.conj w) Γ'' Γ hw'' φ g, MulAut.conj_apply, map_mul, map_mul,
    map_inv, mul_inv_cancel_comm]

theorem iwahori_one_group (Γ Γ'' : Subgroup G) [Γ.FiniteIndex] [Γ''.FiniteIndex] (w : G)
    (hw : ∀ x, x ∈ Γ ↔ w⁻¹ * x * w ∈ Γ'')
    (hdec : ∀ g : G, w⁻¹ * g ∈ Γ'' ∨ ∃ l ∈ Γ, l⁻¹ * g ∈ Γ'')
    (hnot : ∀ l ∈ Γ, l⁻¹ * w ∉ Γ'')
    (φ : Γ →* C) (x : Γ) :
    MonoidHom.transfer
        ((MonoidHom.transfer (φ.comp (inclSubgroupOf Γ'' Γ))).comp (inclSubgroupOf Γ Γ'')) x
      = φ x * (MonoidHom.transfer φ (x : G)) ^ (Γ''.index - 2) := by

  have hw' : ∀ y ∈ Γ'', (w⁻¹)⁻¹ * y * w⁻¹ ∈ Γ := by
    intro y hy
    rw [hw, inv_inv]
    simpa only [← mul_assoc, inv_mul_cancel, one_mul, inv_mul_cancel_right] using hy
  have hw'' : ∀ y, y ∈ Γ'' ↔ (MulAut.conj w) y ∈ Γ := by
    intro y
    rw [MulAut.conj_apply, hw]
    simp only [← mul_assoc, inv_mul_cancel, one_mul, inv_mul_cancel_right]
  have hdec' : ∀ g : G, (w⁻¹)⁻¹ * g ∈ Γ ∨ ∃ l ∈ Γ'', l⁻¹ * g ∈ Γ := by
    intro g
    rcases hdec g⁻¹ with h | ⟨l, hl, hlg⟩
    · left
      have h2 := hw' _ (Γ''.inv_mem h)
      simpa only [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel, mul_one] using h2
    · right
      refine ⟨g * l, ?_, ?_⟩
      · simpa only [mul_inv_rev, inv_inv] using Γ''.inv_mem hlg
      · rw [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
        exact Γ.inv_mem hl
  have hnot' : ∀ l ∈ Γ'', l⁻¹ * w⁻¹ ∉ Γ := by
    intro l hl hmem
    have h1 : w⁻¹ * (l⁻¹ * w⁻¹) * w ∈ Γ'' := (hw _).mp hmem
    rw [mul_assoc, mul_assoc, inv_mul_cancel, mul_one] at h1
    have h2 : w⁻¹ ∈ Γ'' := by simpa using Γ''.mul_mem h1 hl
    exact hnot 1 Γ.one_mem (by simpa using Γ''.inv_mem h2)

  set J : G →* C := MonoidHom.transfer φ with hJ
  set cφ : Γ'' →* C := φ.comp (restrictEquiv (MulAut.conj w) Γ'' Γ hw'') with hcφ

  have hΨ : MonoidHom.transfer (φ.comp (inclSubgroupOf Γ'' Γ)) = J.domRestrict Γ'' * cφ⁻¹ := by
    ext y
    have hm := transfer_mackey_two Γ'' Γ w⁻¹ hw' hdec' hnot' φ y
    have hc : φ ⟨w⁻¹⁻¹ * ↑y * w⁻¹, hw' y y.2⟩ = cφ y := by
      rw [hcφ, MonoidHom.comp_apply]; congr 1; apply Subtype.ext
      simp only [coe_restrictEquiv, MulAut.conj_apply, inv_inv]
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.domRestrict_apply, hJ, hm, hc,
      mul_inv_cancel_right]

  have hJc : MonoidHom.transfer cφ = J := by
    ext g; rw [hcφ, hJ]; exact transfer_comp_conj Γ Γ'' w hw'' φ g
  have hJx : J (w⁻¹ * x * w) = J x := by
    rw [map_mul, map_mul, map_inv, inv_mul_cancel_comm]

  have hm := transfer_mackey_two Γ Γ'' w (fun x hx => (hw x).mp hx) hdec hnot
    (MonoidHom.transfer (φ.comp (inclSubgroupOf Γ'' Γ))) x
  have hm' := eq_mul_inv_iff_mul_eq.mpr hm.symm
  rw [hm', hΨ, transfer_mul', transfer_inv', hJc, MonoidHom.mul_apply, MonoidHom.inv_apply,
    MonoidHom.mul_apply, MonoidHom.inv_apply, transfer_restrict_eq_pow, MonoidHom.domRestrict_apply]
  simp only [hJx]
  have hcx : cφ ⟨w⁻¹ * x * w, (hw x).mp x.2⟩ = φ x := by
    rw [hcφ, MonoidHom.comp_apply]
    congr 1
    apply Subtype.ext
    simp only [coe_restrictEquiv, MulAut.conj_apply, ← mul_assoc, mul_inv_cancel, one_mul,
      mul_inv_cancel_right]
  rw [hcx]

  have hne : Γ'' ≠ ⊤ := by
    intro h
    exact hnot 1 Γ.one_mem (h ▸ Subgroup.mem_top _)
  obtain ⟨m, hm2⟩ : ∃ m, Γ''.index = m + 2 :=
    ⟨Γ''.index - 2, by have := Subgroup.one_lt_index_of_ne_top hne; omega⟩
  rw [hm2, Nat.add_sub_cancel, pow_succ, pow_succ, mul_inv_rev, inv_inv, mul_inv_cancel_right,
    mul_comm (φ x) (J ↑x)⁻¹, ← mul_assoc, mul_inv_cancel_right, mul_comm]

end OneGroup

section TwoGroup

variable {G G' : Type*} [Group G] [Group G'] {C : Type*} [CommGroup C]

theorem iwahori_two_group (ι₁ ιq : G →* G') (h₁ : Function.Injective ι₁)
    (hq : Function.Injective ιq) [ι₁.range.FiniteIndex] [ιq.range.FiniteIndex]
    (K₁ K₂ : Subgroup G) [K₁.FiniteIndex] [K₂.FiniteIndex]
    (hK₁ : ∀ k, k ∈ K₁ ↔ ιq k ∈ ι₁.range) (hK₂ : ∀ k, k ∈ K₂ ↔ ι₁ k ∈ ιq.range)
    (c : K₂ →* G) (hc : ∀ k, ιq (c k) = ι₁ k)
    (c' : K₁ →* G) (hc' : ∀ k, ι₁ (c' k) = ιq k)
    (w : G') (hw : ∀ x, x ∈ ι₁.range ↔ w⁻¹ * x * w ∈ ιq.range)
    (hdec : ∀ g : G', w⁻¹ * g ∈ ιq.range ∨ ∃ l ∈ ι₁.range, l⁻¹ * g ∈ ιq.range)
    (hnot : ∀ l ∈ ι₁.range, l⁻¹ * w ∉ ιq.range)
    (φ : G →* C) (g : G) :
    MonoidHom.transfer ((MonoidHom.transfer (φ.comp c')).comp c) g
      = φ g * (MonoidHom.transfer (φ.comp (MonoidHom.ofInjective h₁).symm.toMonoidHom) (ι₁ g))
          ^ (ιq.range.index - 2) := by
  set L₁ := ι₁.range with hL₁
  set Lq := ιq.range with hLq
  set e₁ : G ≃* L₁ := MonoidHom.ofInjective h₁ with he₁
  set eq : G ≃* Lq := MonoidHom.ofInjective hq with heq
  set φ₁ : L₁ →* C := φ.comp e₁.symm.toMonoidHom with hφ₁
  have ce₁ : ∀ k, (e₁ k : G') = ι₁ k := fun k => rfl
  have ceq : ∀ k, (eq k : G') = ιq k := fun k => rfl

  have hK'' : ∀ k, k ∈ K₁ ↔ eq k ∈ L₁.subgroupOf Lq := by
    intro k; rw [Subgroup.mem_subgroupOf, ceq]; exact hK₁ k
  set χ'' : ↥(L₁.subgroupOf Lq) →* C := φ₁.comp (inclSubgroupOf Lq L₁) with hχ''
  have h1 : φ.comp c' = χ''.comp (restrictEquiv eq K₁ (L₁.subgroupOf Lq) hK'') := by
    ext k
    simp only [MonoidHom.comp_apply, hχ'', hφ₁, MulEquiv.coe_toMonoidHom]
    congr 1
    rw [MulEquiv.eq_symm_apply]
    apply Subtype.ext
    rw [ce₁, hc', coe_inclSubgroupOf, coe_restrictEquiv, ceq]
  have h1' : MonoidHom.transfer (φ.comp c') = (MonoidHom.transfer χ'').comp eq.toMonoidHom := by
    ext k
    rw [h1, transfer_comp_equiv, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]

  have hK' : ∀ k, k ∈ K₂ ↔ e₁ k ∈ Lq.subgroupOf L₁ := by
    intro k; rw [Subgroup.mem_subgroupOf, ce₁]; exact hK₂ k
  set Ψ : ↥(Lq.subgroupOf L₁) →* C := (MonoidHom.transfer χ'').comp (inclSubgroupOf L₁ Lq) with hΨ
  have h2 : ((MonoidHom.transfer χ'').comp eq.toMonoidHom).comp c
      = Ψ.comp (restrictEquiv e₁ K₂ (Lq.subgroupOf L₁) hK') := by
    ext k
    simp only [MonoidHom.comp_apply, hΨ, MulEquiv.coe_toMonoidHom]
    congr 1
    apply Subtype.ext
    rw [ceq, hc, coe_inclSubgroupOf, coe_restrictEquiv, ce₁]
  rw [h1', h2, transfer_comp_equiv, hΨ, hχ'',
    iwahori_one_group L₁ Lq w hw hdec hnot φ₁ (e₁ g)]
  simp only [hφ₁, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply, ce₁]

end TwoGroup

section Concrete

open CohCarrier CongruenceSubgroup
open scoped MatrixGroups

variable (M q : ℕ) [NeZero M] [NeZero q]

theorem levelLE_q : LevelLE M (M * q) (⊤ : Subgroup (ZMod M)ˣ) (⊤ : Subgroup (ZMod (M * q))ˣ) q :=
  ⟨dvd_mul_right M q, by rw [Nat.mul_div_cancel_left q (Nat.pos_of_ne_zero (NeZero.ne M))],
    fun _ _ => Subgroup.mem_top _⟩

variable {M q}

@[scoped simp] theorem conjLowerMat_apply_01 (d : ℕ) (A : SL(2, ℤ)) (h : (d : ℤ) ∣ A 1 0) :
    (conjLowerMat d A h) 0 1 = A 0 1 * d := by
  simp [conjLowerMat]

@[scoped simp] theorem conjLowerMat_apply_10 (d : ℕ) (A : SL(2, ℤ)) (h : (d : ℤ) ∣ A 1 0) :
    (conjLowerMat d A h) 1 0 = A 1 0 / d := by
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

theorem mem_GammaHUpper_iff_iotaDeg
    (h1 : LevelLE M (M * q) (⊤ : Subgroup (ZMod M)ˣ) (⊤ : Subgroup (ZMod (M * q))ˣ) 1)
    (hq' : LevelLE M (M * q) (⊤ : Subgroup (ZMod M)ˣ) (⊤ : Subgroup (ZMod (M * q))ˣ) q)
    (k : ↥(GammaH (M * q) ⊤)) :
    k ∈ GammaHUpper (M * q) ⊤ q ↔
      iotaDeg M (M * q) ⊤ ⊤ 1 h1 k ∈ (iotaDeg M (M * q) ⊤ ⊤ q hq').range := by
  rw [mem_range_iotaDeg_q_iff, coe_iotaDeg_one h1, Subgroup.mem_subgroupOf, mem_Gamma0Upper,
    ZMod.intCast_zmod_eq_zero_iff_dvd]

theorem mem_GammaHLower_iff_iotaDeg
    (h1 : LevelLE M (M * q) (⊤ : Subgroup (ZMod M)ˣ) (⊤ : Subgroup (ZMod (M * q))ˣ) 1)
    (hq' : LevelLE M (M * q) (⊤ : Subgroup (ZMod M)ˣ) (⊤ : Subgroup (ZMod (M * q))ˣ) q)
    (k : ↥(GammaH (M * q) ⊤)) :
    k ∈ GammaHLower (M * q) ⊤ q ↔
      iotaDeg M (M * q) ⊤ ⊤ q hq' k ∈ (iotaDeg M (M * q) ⊤ ⊤ 1 h1).range := by
  rw [mem_range_iotaDeg_one_iff, Subgroup.mem_subgroupOf, Gamma0_mem, Gamma0_mem,
    ZMod.intCast_zmod_eq_zero_iff_dvd, ZMod.intCast_zmod_eq_zero_iff_dvd]
  show ((q * (M * q) : ℕ) : ℤ) ∣ (k : SL(2, ℤ)) 1 0 ↔
    ((M * q : ℕ) : ℤ) ∣ (conjLowerMat q (k : SL(2, ℤ)) (hq'.dvd_entry k)) 1 0
  rw [conjLowerMat_apply_10]
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne q
  conv_lhs => rw [← Int.mul_ediv_cancel' (hq'.dvd_entry k)]
  push_cast
  exact mul_dvd_mul_iff_left hq0

theorem iotaDeg_q_conjL
    (h1 : LevelLE M (M * q) (⊤ : Subgroup (ZMod M)ˣ) (⊤ : Subgroup (ZMod (M * q))ˣ) 1)
    (hq' : LevelLE M (M * q) (⊤ : Subgroup (ZMod M)ˣ) (⊤ : Subgroup (ZMod (M * q))ˣ) q)
    (k : ↥(GammaHUpper (M * q) ⊤ q)) :
    iotaDeg M (M * q) ⊤ ⊤ q hq' (conjL (M * q) ⊤ q k) = iotaDeg M (M * q) ⊤ ⊤ 1 h1 k := by
  apply Subtype.ext
  rw [coe_iotaDeg_one h1]
  exact conjLowerMat_conjUpperMat q ((k : ↥(GammaH (M * q) ⊤)) : SL(2, ℤ))
    (dvd_of_mem_GammaHUpper (M * q) ⊤ q k) (hq'.dvd_entry (conjL (M * q) ⊤ q k))

theorem iotaDeg_one_conjLowerL
    (h1 : LevelLE M (M * q) (⊤ : Subgroup (ZMod M)ˣ) (⊤ : Subgroup (ZMod (M * q))ˣ) 1)
    (hq' : LevelLE M (M * q) (⊤ : Subgroup (ZMod M)ˣ) (⊤ : Subgroup (ZMod (M * q))ˣ) q)
    (k : ↥(GammaHLower (M * q) ⊤ q)) :
    iotaDeg M (M * q) ⊤ ⊤ 1 h1 (conjLowerL (M * q) ⊤ q k) = iotaDeg M (M * q) ⊤ ⊤ q hq' k := by
  apply Subtype.ext
  rw [coe_iotaDeg_one h1]
  rfl

def wMat (u v : ℤ) (huv : u * q + v * M = 1) : SL(2, ℤ) :=
  ⟨!![u, -v; (M : ℤ), (q : ℤ)], by rw [Matrix.det_fin_two_of]; linear_combination huv⟩

theorem wMat_mem (u v : ℤ) (huv : u * q + v * M = 1) : wMat (M := M) (q := q) u v huv ∈ GammaH M ⊤ := by
  rw [GammaH_top, Gamma0_mem]
  show (((M : ℤ)) : ZMod M) = 0
  rw [Int.cast_natCast, ZMod.natCast_self]

def wElt (u v : ℤ) (huv : u * q + v * M = 1) : ↥(GammaH M ⊤) := ⟨wMat u v huv, wMat_mem u v huv⟩

section entries

variable (u v : ℤ) (huv : u * q + v * M = 1)

private theorem mul_apply' (x y : SL(2, ℤ)) (i j : Fin 2) :
    (x * y : SL(2, ℤ)) i j = x i 0 * y 0 j + x i 1 * y 1 j := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

private theorem inv_apply' (x : SL(2, ℤ)) :
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

end Concrete

section Assembly

open CohCarrier CongruenceSubgroup
open scoped MatrixGroups

variable {M q : ℕ} [NeZero M] [NeZero q]

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

theorem index_GammaHUpper_mul : (GammaHUpper (M * q) ⊤ q).index = q := by
  rw [Subgroup.index_eq_card,
    ← Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel (GammaHUpper (M * q) ⊤ q)),
    ← Nat.card_congr (rightQuotEquivOfDvd (M * q) ⊤ q (dvd_mul_left q M)), Nat.card_zmod]

theorem index_range_iotaDeg_q (hq : q.Prime) (u v : ℤ) (huv : u * q + v * M = 1)
    (h1 : LevelLE M (M * q) (⊤ : Subgroup (ZMod M)ˣ) (⊤ : Subgroup (ZMod (M * q))ˣ) 1)
    (hq' : LevelLE M (M * q) (⊤ : Subgroup (ZMod M)ˣ) (⊤ : Subgroup (ZMod (M * q))ˣ) q) :
    (iotaDeg M (M * q) ⊤ ⊤ q hq').range.index = q + 1 := by
  have hK' : ∀ k, k ∈ GammaHUpper (M * q) ⊤ q ↔
      MonoidHom.ofInjective (iotaDeg_injective M (M * q) ⊤ ⊤ 1 h1) k ∈
        ((iotaDeg M (M * q) ⊤ ⊤ q hq').range).subgroupOf (iotaDeg M (M * q) ⊤ ⊤ 1 h1).range := by
    intro k
    rw [Subgroup.mem_subgroupOf]
    exact mem_GammaHUpper_iff_iotaDeg h1 hq' k
  rw [index_eq_index_subgroupOf_add_one _ _ (wElt u v huv) (hdec_wElt hq u v huv h1 hq')
      (hnot_wElt hq u v huv h1 hq'),
    ← index_eq_of_equiv _ _ _ hK', index_GammaHUpper_mul]

theorem main (hq : q.Prime) (hqM : ¬ q ∣ M) (A : Type) [AddCommGroup A]
    (h1 : LevelLE M (M * q) (⊤ : Subgroup (ZMod M)ˣ) (⊤ : Subgroup (ZMod (M * q))ˣ) 1)
    (φ : H1 (M * q) ⊤ A) :
    heckeT (M * q) ⊤ q A (heckeTlower (M * q) ⊤ q A φ)
      = φ + (q - 1) • iDeg' M (M * q) ⊤ ⊤ 1 A h1 (jDeg M (M * q) ⊤ ⊤ 1 A h1 φ) := by
  have hq' := levelLE_q M q
  have hcop : IsCoprime (q : ℤ) (M : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqM)
  obtain ⟨u, v, huv⟩ := hcop
  refine AddMonoidHom.ext fun a => ?_
  have key := iwahori_two_group (C := Multiplicative A)
    (iotaDeg M (M * q) ⊤ ⊤ 1 h1) (iotaDeg M (M * q) ⊤ ⊤ q hq')
    (iotaDeg_injective M (M * q) ⊤ ⊤ 1 h1) (iotaDeg_injective M (M * q) ⊤ ⊤ q hq')
    (GammaHLower (M * q) ⊤ q) (GammaHUpper (M * q) ⊤ q)
    (mem_GammaHLower_iff_iotaDeg h1 hq') (mem_GammaHUpper_iff_iotaDeg h1 hq')
    (conjL (M * q) ⊤ q) (iotaDeg_q_conjL h1 hq')
    (conjLowerL (M * q) ⊤ q) (iotaDeg_one_conjLowerL h1 hq')
    (wElt u v huv) (hw_wElt u v huv h1 hq') (hdec_wElt hq u v huv h1 hq')
    (hnot_wElt hq u v huv h1 hq')
    (AddMonoidHom.toMultiplicativeRight φ) (Additive.toMul a)
  have e1 : AddMonoidHom.toMultiplicativeRight (heckeTlower (M * q) ⊤ q A φ)
      = MonoidHom.transfer
          ((AddMonoidHom.toMultiplicativeRight φ).comp (conjLowerL (M * q) ⊤ q)) :=
    Equiv.apply_symm_apply _ _
  have e2 : AddMonoidHom.toMultiplicativeRight (pushChar M (M * q) ⊤ ⊤ 1 A h1 φ)
      = (AddMonoidHom.toMultiplicativeRight φ).comp
          (MonoidHom.ofInjective (iotaDeg_injective M (M * q) ⊤ ⊤ 1 h1)).symm.toMonoidHom :=
    MonoidHom.ext fun _ => rfl
  show Multiplicative.toAdd (MonoidHom.transfer
      ((AddMonoidHom.toMultiplicativeRight (heckeTlower (M * q) ⊤ q A φ)).comp (conjL (M * q) ⊤ q))
      (Additive.toMul a))
    = φ a + (q - 1) • Multiplicative.toAdd (MonoidHom.transfer
        (AddMonoidHom.toMultiplicativeRight (pushChar M (M * q) ⊤ ⊤ 1 A h1 φ))
        (iotaDeg M (M * q) ⊤ ⊤ 1 h1 (Additive.toMul a)))
  rw [e1, e2, key, toAdd_mul, toAdd_pow, index_range_iotaDeg_q hq u v huv h1 hq',
    show q + 1 - 2 = q - 1 by omega]
  rfl

end Assembly

end IwahoriQuadSol
p2m_reactivate "P2MW.S_CohCarrier_heckeT_heckeTlower_eq_add_smul_iDeg_jDeg_of_prime.IwahoriQuadSol"

open CohCarrier in
theorem solution (M q : ℕ) [NeZero M]
    [NeZero q] (A : Type) [AddCommGroup A] (hq : q.Prime) (hqM : ¬ q ∣ M)
    (h1 : LevelLE M (M * q) (⊤ : Subgroup (ZMod M)ˣ) (⊤ : Subgroup (ZMod (M * q))ˣ) 1)
    (φ : H1 (M * q) ⊤ A) :
    heckeT (M * q) ⊤ q A (heckeTlower (M * q) ⊤ q A φ)
      = φ + (q - 1) • iDeg' M (M * q) ⊤ ⊤ 1 A h1 (jDeg M (M * q) ⊤ ⊤ 1 A h1 φ) :=
  IwahoriQuadSol.main hq hqM A h1 φ

end S_CohCarrier_heckeT_heckeTlower_eq_add_smul_iDeg_jDeg_of_prime
end P2MW
export P2MW.S_CohCarrier_heckeT_heckeTlower_eq_add_smul_iDeg_jDeg_of_prime (solution)
