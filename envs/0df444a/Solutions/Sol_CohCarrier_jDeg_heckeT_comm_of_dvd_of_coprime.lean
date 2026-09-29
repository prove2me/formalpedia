-- Prove2me | solution 1 for CohCarrier.jDeg_heckeT_comm_of_dvd_of_coprime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/b48a9f28-9aa2-52c0-bce0-d3580641fd3c

import Mathlib
import Definitions.Def_CohCarrier_Level
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_jDeg_heckeT_comm_of_dvd_of_coprime

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

namespace JDegHeckeUCoprimeSol

section SectionFormula

variable {G : Type*} [Group G] {A : Type*} [CommGroup A]

theorem section_term_mem (K : Subgroup G) (s : G ⧸ K → G) (hs : ∀ q, (s q : G ⧸ K) = q)
    (g : G) (q : G ⧸ K) : (s q)⁻¹ * g * s (g⁻¹ • q) ∈ K := by
  have h1 : ((g * s (g⁻¹ • q) : G) : G ⧸ K) = q := by
    rw [← smul_eq_mul, ← MulAction.Quotient.smul_coe, hs, smul_inv_smul]
  rw [mul_assoc, ← QuotientGroup.eq, hs, h1]

theorem transfer_eq_prod_section (K : Subgroup G) [K.FiniteIndex] (ϕ : K →* A)
    (s : G ⧸ K → G) (hs : ∀ q, (s q : G ⧸ K) = q) (g : G) :
    MonoidHom.transfer ϕ g =
      ∏ q : G ⧸ K, ϕ ⟨(s q)⁻¹ * g * s (g⁻¹ • q), section_term_mem K s hs g q⟩ := by
  let T : K.LeftTransversal := ⟨Set.range s, Subgroup.isComplement_range_left hs⟩
  rw [MonoidHom.transfer_def ϕ T g]
  simp only [Subgroup.leftTransversals.diff]
  refine Finset.prod_congr rfl fun q _ => ?_
  congr 1
  apply Subtype.ext
  show ((T.2.leftQuotientEquiv q : G))⁻¹ * ((g • T).2.leftQuotientEquiv q : G) =
    (s q)⁻¹ * g * s (g⁻¹ • q)
  rw [Subgroup.smul_apply_eq_smul_apply_inv_smul,
    Subgroup.IsComplement.leftQuotientEquiv_apply hs,
    Subgroup.IsComplement.leftQuotientEquiv_apply hs, smul_eq_mul, mul_assoc]

end SectionFormula

section Naturality

variable {G : Type*} [Group G] {K : Type*} [Group K] {A : Type*} [CommGroup A]
  (f : K →* G) (L : Subgroup G)

def quotMapHom : K ⧸ L.comap f → G ⧸ L :=
  Quotient.map' (fun k : K => f k) fun a b hab => by
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    rw [Subgroup.mem_comap, map_mul, map_inv] at hab
    exact hab

theorem quotMapHom_mk (k : K) : quotMapHom f L (QuotientGroup.mk k) = QuotientGroup.mk (f k) :=
  rfl

theorem quotMapHom_injective : Function.Injective (quotMapHom f L) := by
  intro a b
  induction a using QuotientGroup.induction_on with
  | H x =>
    induction b using QuotientGroup.induction_on with
    | H y =>
      intro hxy
      rw [quotMapHom_mk, quotMapHom_mk, QuotientGroup.eq] at hxy
      rw [QuotientGroup.eq, Subgroup.mem_comap, map_mul, map_inv]
      exact hxy

theorem quotMapHom_surjective (hf : ∀ g : G, ∃ k : K, (f k)⁻¹ * g ∈ L) :
    Function.Surjective (quotMapHom f L) := by
  intro q
  induction q using QuotientGroup.induction_on with
  | H g =>
    obtain ⟨k, hk⟩ := hf g
    exact ⟨QuotientGroup.mk k, by rw [quotMapHom_mk, QuotientGroup.eq]; exact hk⟩

theorem quotMapHom_smul (k : K) (q : K ⧸ L.comap f) :
    quotMapHom f L (k • q) = f k • quotMapHom f L q := by
  induction q using QuotientGroup.induction_on with
  | H x =>
    rw [MulAction.Quotient.smul_mk, quotMapHom_mk, quotMapHom_mk, MulAction.Quotient.smul_mk,
      smul_eq_mul, smul_eq_mul, map_mul]

theorem finiteIndex_comap_of_forall_exists [L.FiniteIndex]
    (hf : ∀ g : G, ∃ k : K, (f k)⁻¹ * g ∈ L) : (L.comap f).FiniteIndex := by
  haveI : Finite (K ⧸ L.comap f) := Finite.of_injective _ (quotMapHom_injective f L)
  exact Subgroup.finiteIndex_of_finite_quotient

theorem transfer_apply_eq_transfer_comap [L.FiniteIndex] [(L.comap f).FiniteIndex]
    (hf : ∀ g : G, ∃ k : K, (f k)⁻¹ * g ∈ L) (ϕ : L →* A) (k : K) :
    MonoidHom.transfer ϕ (f k) = MonoidHom.transfer (ϕ.comp (f.subgroupComap L)) k := by
  classical
  set Θ : K ⧸ L.comap f ≃ G ⧸ L :=
    Equiv.ofBijective (quotMapHom f L) ⟨quotMapHom_injective f L, quotMapHom_surjective f L hf⟩
    with hΘ
  have hΘmk : ∀ x : K, Θ (QuotientGroup.mk x) = QuotientGroup.mk (f x) := fun x => rfl
  have hΘsmul : ∀ (x : K) (q : K ⧸ L.comap f), Θ (x • q) = f x • Θ q :=
    fun x q => quotMapHom_smul f L x q

  set sK : K ⧸ L.comap f → K := Quotient.out with hsK
  have hsK' : ∀ y, (sK y : K ⧸ L.comap f) = y := fun y => Quotient.out_eq y
  set sG : G ⧸ L → G := fun p => f (sK (Θ.symm p)) with hsG
  have hsG' : ∀ p, (sG p : G ⧸ L) = p := by
    intro p
    show QuotientGroup.mk (f (sK (Θ.symm p))) = p
    rw [← hΘmk, hsK', Equiv.apply_symm_apply]
  rw [transfer_eq_prod_section L ϕ sG hsG' (f k),
    transfer_eq_prod_section (L.comap f) _ sK hsK' k]
  refine (Fintype.prod_equiv Θ _ _ fun y => ?_).symm
  rw [MonoidHom.comp_apply]
  congr 1
  apply Subtype.ext
  show f ((sK y)⁻¹ * k * sK (k⁻¹ • y)) = (sG (Θ y))⁻¹ * f k * sG ((f k)⁻¹ • Θ y)
  have e1 : (f k)⁻¹ • Θ y = Θ (k⁻¹ • y) := by rw [hΘsmul, map_inv]
  rw [e1, hsG]
  simp only [Equiv.symm_apply_apply, map_mul, map_inv]

end Naturality

section Transitivity

variable {G : Type*} [Group G] {A : Type*} [CommGroup A]
  (L : Subgroup G) (K : Subgroup L)

theorem finiteIndex_map_subtype [L.FiniteIndex] [K.FiniteIndex] :
    (K.map L.subtype).FiniteIndex := by
  rw [Subgroup.finiteIndex_iff, Subgroup.index_map_subtype]
  exact mul_ne_zero Subgroup.FiniteIndex.index_ne_zero Subgroup.FiniteIndex.index_ne_zero

noncomputable def pushSubtype (ϕ : K →* A) : K.map L.subtype →* A :=
  ϕ.comp (Subgroup.equivMapOfInjective K L.subtype L.subtype_injective).symm.toMonoidHom

theorem pushSubtype_apply (ϕ : K →* A) (x : K) (hx : ((x : L) : G) ∈ K.map L.subtype) :
    pushSubtype L K ϕ ⟨((x : L) : G), hx⟩ = ϕ x := by
  have : (⟨((x : L) : G), hx⟩ : K.map L.subtype) =
      Subgroup.equivMapOfInjective K L.subtype L.subtype_injective x := Subtype.ext rfl
  rw [this, pushSubtype, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]

theorem transfer_transfer_apply [L.FiniteIndex] [K.FiniteIndex] [(K.map L.subtype).FiniteIndex]
    (ϕ : K →* A) (g : G) :
    MonoidHom.transfer (MonoidHom.transfer ϕ : L →* A) g =
      MonoidHom.transfer (pushSubtype L K ϕ) g := by
  classical
  set KG : Subgroup G := K.map L.subtype with hKG

  set sL : G ⧸ L → G := Quotient.out with hsL
  have hsL' : ∀ p, (sL p : G ⧸ L) = p := fun p => Quotient.out_eq p
  set sK : L ⧸ K → L := Quotient.out with hsK
  have hsK' : ∀ x, (sK x : L ⧸ K) = x := fun x => Quotient.out_eq x
  have hmemL : ∀ (p : G ⧸ L) (g' : G), (p : G ⧸ L) = QuotientGroup.mk g' → (sL p)⁻¹ * g' ∈ L := by
    intro p g' hp
    rw [← QuotientGroup.eq, hsL', hp]

  set θ : (G ⧸ L) × (L ⧸ K) → G ⧸ KG := fun px => QuotientGroup.mk (sL px.1 * (sK px.2 : G))
    with hθ
  have hθ_apply : ∀ px : (G ⧸ L) × (L ⧸ K), θ px = QuotientGroup.mk (sL px.1 * (sK px.2 : G)) :=
    fun _ => rfl

  have hmemKG : ∀ y : L, (y : G) ∈ KG ↔ y ∈ K := by
    intro y
    constructor
    · rintro ⟨z, hz, hzy⟩
      have : z = y := Subtype.ext hzy
      rw [← this]; exact hz
    · intro hy; exact ⟨y, hy, rfl⟩
  have hproj : ∀ (p : G ⧸ L) (x : L ⧸ K),
      (QuotientGroup.mk (sL p * (sK x : G)) : G ⧸ L) = p := by
    intro p x
    rw [← smul_eq_mul, ← MulAction.Quotient.smul_coe]
    have : ((sK x : G) : G ⧸ L) = QuotientGroup.mk (1 : G) := by
      rw [QuotientGroup.eq, mul_one]; exact L.inv_mem (sK x).2
    rw [this, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, hsL']
  have hθinj : Function.Injective θ := by
    rintro ⟨p, x⟩ ⟨p', x'⟩ hpp
    rw [hθ_apply, hθ_apply] at hpp
    simp only at hpp

    have hp : p = p' := by
      have h1 := congrArg (Quotient.map' id fun (a b : G) (hab : QuotientGroup.leftRel KG a b) =>
        show QuotientGroup.leftRel L (id a) (id b) from by
          rw [QuotientGroup.leftRel_apply] at hab ⊢
          exact Subgroup.map_subtype_le K hab) hpp
      change (QuotientGroup.mk (sL p * (sK x : G)) : G ⧸ L) =
        QuotientGroup.mk (sL p' * (sK x' : G)) at h1
      rwa [hproj, hproj] at h1
    subst hp
    rw [QuotientGroup.eq] at hpp
    have h2 : (((sK x)⁻¹ * sK x' : L) : G) ∈ KG := by
      have : (((sK x)⁻¹ * sK x' : L) : G) = (sL p * (sK x : G))⁻¹ * (sL p * (sK x' : G)) := by
        simp only [Subgroup.coe_mul, InvMemClass.coe_inv]; group
      rw [this]; exact hpp
    rw [hmemKG, ← QuotientGroup.eq, hsK', hsK'] at h2
    rw [h2]
  have hθsurj : Function.Surjective θ := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H g =>
      set p : G ⧸ L := QuotientGroup.mk g
      set y : L := ⟨(sL p)⁻¹ * g, hmemL p g rfl⟩
      refine ⟨(p, QuotientGroup.mk y), ?_⟩
      rw [hθ_apply, QuotientGroup.eq]
      obtain hk := (QuotientGroup.eq (s := K)).mp (hsK' (QuotientGroup.mk y))

      have : (sL p * (sK (QuotientGroup.mk y) : G))⁻¹ * g =
          (((sK (QuotientGroup.mk y))⁻¹ * y : L) : G) := by
        simp only [Subgroup.coe_mul, InvMemClass.coe_inv, y]; group
      rw [this, hmemKG]
      exact hk
  set Θ : (G ⧸ L) × (L ⧸ K) ≃ G ⧸ KG := Equiv.ofBijective θ ⟨hθinj, hθsurj⟩ with hΘ
  have hΘapply : ∀ px, Θ px = θ px := fun _ => rfl

  set s : G ⧸ KG → G := fun q => sL (Θ.symm q).1 * (sK (Θ.symm q).2 : G) with hs
  have hs' : ∀ q, (s q : G ⧸ KG) = q := by
    intro q
    show QuotientGroup.mk (sL (Θ.symm q).1 * (sK (Θ.symm q).2 : G)) = q
    rw [← hθ_apply, ← hΘapply, Equiv.apply_symm_apply]
  have hsΘ : ∀ px, s (Θ px) = sL px.1 * (sK px.2 : G) := by
    intro px; rw [hs]; simp only [Equiv.symm_apply_apply]

  have houtmem : ∀ p : G ⧸ L, (sL p)⁻¹ * g * sL (g⁻¹ • p) ∈ L := section_term_mem L sL hsL' g
  set lp : G ⧸ L → L := fun p => ⟨(sL p)⁻¹ * g * sL (g⁻¹ • p), houtmem p⟩ with hlp

  have hΘsmul : ∀ (p : G ⧸ L) (x : L ⧸ K), g⁻¹ • Θ (p, x) = Θ (g⁻¹ • p, (lp p)⁻¹ • x) := by
    intro p x
    rw [hΘapply, hΘapply, hθ_apply, hθ_apply]
    simp only
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq]
    obtain hk := (QuotientGroup.eq (s := K)).mp
      ((hsK' ((lp p)⁻¹ • x)).trans (by rw [← hsK' x, MulAction.Quotient.smul_mk, hsK' x] :
        (lp p)⁻¹ • x = QuotientGroup.mk ((lp p)⁻¹ • sK x)))

    have : (g⁻¹ * (sL p * (sK x : G)))⁻¹ * (sL (g⁻¹ • p) * (sK ((lp p)⁻¹ • x) : G)) =
        ((((sK ((lp p)⁻¹ • x))⁻¹ * ((lp p)⁻¹ • sK x) : L) : G))⁻¹ := by
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv, smul_eq_mul, hlp]; group
    rw [this]
    exact KG.inv_mem ((hmemKG _).mpr hk)

  rw [transfer_eq_prod_section KG _ s hs' g, transfer_eq_prod_section L _ sL hsL' g]
  rw [← Fintype.prod_equiv Θ (fun px => pushSubtype L K ϕ
      ⟨(s (Θ px))⁻¹ * g * s (g⁻¹ • Θ px), section_term_mem KG s hs' g (Θ px)⟩) _ (fun _ => rfl),
    Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [transfer_eq_prod_section K ϕ sK hsK' (lp p)]
  refine Finset.prod_congr rfl fun x _ => ?_
  have hmem : (((sK x)⁻¹ * lp p * sK ((lp p)⁻¹ • x) : L) : G) ∈ KG :=
    (hmemKG _).mpr (section_term_mem K sK hsK' (lp p) x)
  rw [← pushSubtype_apply L K ϕ _ hmem]
  congr 1
  apply Subtype.ext
  show (((sK x)⁻¹ * lp p * sK ((lp p)⁻¹ • x) : L) : G) = (s (Θ (p, x)))⁻¹ * g * s (g⁻¹ • Θ (p, x))
  rw [hΘsmul, hsΘ, hsΘ]
  simp only [Subgroup.coe_mul, InvMemClass.coe_inv, hlp]
  group

end Transitivity

theorem transfer_congr_of_eq {G : Type*} [Group G] {A : Type*} [CommGroup A]
    {K₁ K₂ : Subgroup G} [K₁.FiniteIndex] [K₂.FiniteIndex] (hK : K₁ = K₂)
    (ψ₁ : K₁ →* A) (ψ₂ : K₂ →* A)
    (hψ : ∀ (x : G) (h₁ : x ∈ K₁) (h₂ : x ∈ K₂), ψ₁ ⟨x, h₁⟩ = ψ₂ ⟨x, h₂⟩) (g : G) :
    MonoidHom.transfer ψ₁ g = MonoidHom.transfer ψ₂ g := by
  subst hK
  have : ψ₁ = ψ₂ := MonoidHom.ext fun x => hψ x x.2 x.2
  subst this
  rfl

section Matrices

open CohCarrier CongruenceSubgroup
open scoped MatrixGroups

variable (d ℓ : ℕ)

@[scoped simp] theorem conjLowerMat_apply_00 (A : SL(2, ℤ)) (hA : (d : ℤ) ∣ A 1 0) :
    (conjLowerMat d A hA) 0 0 = A 0 0 := by
  simp [conjLowerMat]

@[scoped simp] theorem conjLowerMat_apply_01 (A : SL(2, ℤ)) (hA : (d : ℤ) ∣ A 1 0) :
    (conjLowerMat d A hA) 0 1 = A 0 1 * d := by
  simp [conjLowerMat]

@[scoped simp] theorem conjLowerMat_apply_10 (A : SL(2, ℤ)) (hA : (d : ℤ) ∣ A 1 0) :
    (conjLowerMat d A hA) 1 0 = A 1 0 / d := by
  simp [conjLowerMat]

@[scoped simp] theorem conjLowerMat_apply_11 (A : SL(2, ℤ)) (hA : (d : ℤ) ∣ A 1 0) :
    (conjLowerMat d A hA) 1 1 = A 1 1 := by
  simp [conjLowerMat]

@[scoped simp] theorem conjUpperMat_apply_00 (A : SL(2, ℤ)) (hA : (ℓ : ℤ) ∣ A 0 1) :
    (conjUpperMat ℓ A hA) 0 0 = A 0 0 := by
  simp [conjUpperMat]

@[scoped simp] theorem conjUpperMat_apply_01 (A : SL(2, ℤ)) (hA : (ℓ : ℤ) ∣ A 0 1) :
    (conjUpperMat ℓ A hA) 0 1 = A 0 1 / ℓ := by
  simp [conjUpperMat]

theorem SL2_ext' {A B : SL(2, ℤ)} (h00 : A 0 0 = B 0 0) (h01 : A 0 1 = B 0 1)
    (h10 : A 1 0 = B 1 0) (h11 : A 1 1 = B 1 1) : A = B := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

theorem conjUpperMat_conjLowerMat [NeZero ℓ] (A : SL(2, ℤ)) (hc : (ℓ : ℤ) ∣ A 1 0)
    (hb : (ℓ : ℤ) ∣ (conjLowerMat ℓ A hc) 0 1) : conjUpperMat ℓ (conjLowerMat ℓ A hc) hb = A := by
  have hℓ : (ℓ : ℤ) ≠ 0 := by exact_mod_cast (NeZero.ne ℓ)
  apply SL2_ext'
  · rw [conjUpperMat_apply_00, conjLowerMat_apply_00]
  · rw [conjUpperMat_apply_01, conjLowerMat_apply_01, Int.mul_ediv_cancel _ hℓ]
  · rw [conjUpperMat_apply_10, conjLowerMat_apply_10, Int.ediv_mul_cancel hc]
  · rw [conjUpperMat_apply_11, conjLowerMat_apply_11]

theorem conjUpperMat_conjLowerMat_comm (A : SL(2, ℤ)) (hc : (d : ℤ) ∣ A 1 0)
    (hb : (ℓ : ℤ) ∣ A 0 1) (h₁ : (ℓ : ℤ) ∣ (conjLowerMat d A hc) 0 1)
    (h₂ : (d : ℤ) ∣ (conjUpperMat ℓ A hb) 1 0) :
    conjUpperMat ℓ (conjLowerMat d A hc) h₁ = conjLowerMat d (conjUpperMat ℓ A hb) h₂ := by
  apply SL2_ext'
  · rw [conjUpperMat_apply_00, conjLowerMat_apply_00, conjLowerMat_apply_00, conjUpperMat_apply_00]
  · rw [conjUpperMat_apply_01, conjLowerMat_apply_01, conjLowerMat_apply_01, conjUpperMat_apply_01,
      Int.mul_ediv_assoc' _ hb]
  · rw [conjUpperMat_apply_10, conjLowerMat_apply_10, conjLowerMat_apply_10, conjUpperMat_apply_10,
      Int.mul_ediv_assoc' _ hc]
  · rw [conjUpperMat_apply_11, conjLowerMat_apply_11, conjLowerMat_apply_11, conjUpperMat_apply_11]

theorem conjUpperMat_congr {A B : SL(2, ℤ)} (hAB : A = B) (hA : (ℓ : ℤ) ∣ A 0 1) (hB : (ℓ : ℤ) ∣ B 0 1) :
    conjUpperMat ℓ A hA = conjUpperMat ℓ B hB := by
  subst hAB
  rfl

theorem conjLowerMat_congr {A B : SL(2, ℤ)} (hAB : A = B) (hA : (d : ℤ) ∣ A 1 0) (hB : (d : ℤ) ∣ B 1 0) :
    conjLowerMat d A hA = conjLowerMat d B hB := by
  subst hAB
  rfl

theorem SL2_mul_apply (A B : SL(2, ℤ)) (i j : Fin 2) :
    (A * B) i j = A i 0 * B 0 j + A i 1 * B 1 j := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]

end Matrices

section Level

open CohCarrier CongruenceSubgroup
open scoped MatrixGroups

theorem gamma0Units_eq_of_entry_eq {L : ℕ} (x y : ↥(Gamma0 L))
    (hxy : (x : SL(2, ℤ)) 1 1 = (y : SL(2, ℤ)) 1 1) : gamma0Units L x = gamma0Units L y := by
  ext
  simp only [val_gamma0Units]
  show (((x : SL(2, ℤ)) 1 1 : ℤ) : ZMod L) = (((y : SL(2, ℤ)) 1 1 : ℤ) : ZMod L)
  rw [hxy]

theorem gamma0Units_mem_of_mem {L : ℕ} {K : Subgroup (ZMod L)ˣ} {x : SL(2, ℤ)} (hx : x ∈ GammaH L K)
    (hx0 : x ∈ Gamma0 L) : gamma0Units L ⟨x, hx0⟩ ∈ K := by
  obtain ⟨_, hu⟩ := mem_GammaH_iff.mp hx
  exact hu

theorem mem_GammaH_of_entry_eq {L : ℕ} {K : Subgroup (ZMod L)ˣ} {x y : SL(2, ℤ)}
    (hx : x ∈ GammaH L K) (hy0 : y ∈ Gamma0 L) (hxy : x 1 1 = y 1 1) : y ∈ GammaH L K := by
  have hx0 : x ∈ Gamma0 L := GammaH_le_Gamma0 K hx
  refine mem_GammaH_iff.mpr ⟨hy0, ?_⟩
  rw [← gamma0Units_eq_of_entry_eq ⟨x, hx0⟩ ⟨y, hy0⟩ hxy]
  exact gamma0Units_mem_of_mem hx hx0

variable {M M' : ℕ} {H : Subgroup (ZMod M)ˣ} {H' : Subgroup (ZMod M')ˣ} {d : ℕ} [NeZero M'] [NeZero d]
variable (h : LevelLE M M' H H' d)

theorem coe_iotaDeg (γ : ↥(GammaH M' H')) :
    ((iotaDeg M M' H H' d h γ : ↥(GammaH M H)) : SL(2, ℤ)) = conjLowerMat d (γ : SL(2, ℤ)) (h.dvd_entry γ) :=
  rfl

theorem mem_range_iotaDeg_iff (x : ↥(GammaH M H)) :
    x ∈ (iotaDeg M M' H H' d h).range ↔
      ∃ hb : (d : ℤ) ∣ (x : SL(2, ℤ)) 0 1, conjUpperMat d (x : SL(2, ℤ)) hb ∈ GammaH M' H' := by
  constructor
  · rintro ⟨γ, rfl⟩
    have hb : (d : ℤ) ∣ ((iotaDeg M M' H H' d h γ : ↥(GammaH M H)) : SL(2, ℤ)) 0 1 := by
      rw [coe_iotaDeg, conjLowerMat_apply_01]
      exact dvd_mul_left _ _
    refine ⟨hb, ?_⟩
    have : conjUpperMat d ((iotaDeg M M' H H' d h γ : ↥(GammaH M H)) : SL(2, ℤ)) hb = (γ : SL(2, ℤ)) :=
      conjUpperMat_conjLowerMat d (γ : SL(2, ℤ)) (h.dvd_entry γ) hb
    rw [this]
    exact γ.2
  · rintro ⟨hb, hmem⟩
    refine ⟨⟨conjUpperMat d (x : SL(2, ℤ)) hb, hmem⟩, Subtype.ext ?_⟩
    rw [coe_iotaDeg]
    exact conjLowerMat_conjUpperMat d (x : SL(2, ℤ)) hb _

noncomputable def iotaInv : ↥((iotaDeg M M' H H' d h).range) ≃* ↥(GammaH M' H') :=
  (MonoidHom.ofInjective (iotaDeg_injective M M' H H' d h)).symm

theorem iotaInv_apply (γ : ↥(GammaH M' H'))
    (hγ : iotaDeg M M' H H' d h γ ∈ (iotaDeg M M' H H' d h).range) :
    iotaInv h ⟨iotaDeg M M' H H' d h γ, hγ⟩ = γ := by
  have : (⟨iotaDeg M M' H H' d h γ, hγ⟩ : ↥((iotaDeg M M' H H' d h).range)) =
      MonoidHom.ofInjective (iotaDeg_injective M M' H H' d h) γ := Subtype.ext rfl
  rw [this, iotaInv, MulEquiv.symm_apply_apply]

theorem iotaDeg_iotaInv (n : ↥((iotaDeg M M' H H' d h).range)) :
    iotaDeg M M' H H' d h (iotaInv h n) = (n : ↥(GammaH M H)) :=
  MonoidHom.apply_ofInjective_symm (iotaDeg_injective M M' H H' d h) n

theorem coe_iotaInv (n : ↥((iotaDeg M M' H H' d h).range)) :
    conjLowerMat d ((iotaInv h n : ↥(GammaH M' H')) : SL(2, ℤ)) (h.dvd_entry _) =
      ((n : ↥(GammaH M H)) : SL(2, ℤ)) := by
  rw [← coe_iotaDeg h]
  exact congrArg Subtype.val (iotaDeg_iotaInv h n)

theorem iotaInv_entries (n : ↥((iotaDeg M M' H H' d h).range)) :
    ((n : ↥(GammaH M H)) : SL(2, ℤ)) 0 0 = ((iotaInv h n : ↥(GammaH M' H')) : SL(2, ℤ)) 0 0 ∧
    ((n : ↥(GammaH M H)) : SL(2, ℤ)) 0 1 = ((iotaInv h n : ↥(GammaH M' H')) : SL(2, ℤ)) 0 1 * d ∧
    ((n : ↥(GammaH M H)) : SL(2, ℤ)) 1 0 = ((iotaInv h n : ↥(GammaH M' H')) : SL(2, ℤ)) 1 0 / d ∧
    ((n : ↥(GammaH M H)) : SL(2, ℤ)) 1 1 = ((iotaInv h n : ↥(GammaH M' H')) : SL(2, ℤ)) 1 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [← coe_iotaInv h n]
  · rw [conjLowerMat_apply_00]
  · rw [conjLowerMat_apply_01]
  · rw [conjLowerMat_apply_10]
  · rw [conjLowerMat_apply_11]

theorem toMul_pushChar {A : Type} [AddCommGroup A] (ψ : H1 M' H' A) :
    AddMonoidHom.toMultiplicativeRight (pushChar M M' H H' d A h ψ) =
      (AddMonoidHom.toMultiplicativeRight ψ).comp (iotaInv h).toMonoidHom :=
  MonoidHom.ext fun _ => rfl

theorem toMul_jDeg {A : Type} [AddCommGroup A] (ψ : H1 M' H' A) :
    AddMonoidHom.toMultiplicativeRight (jDeg M M' H H' d A h ψ) =
      MonoidHom.transfer ((AddMonoidHom.toMultiplicativeRight ψ).comp (iotaInv h).toMonoidHom) := by
  rw [← toMul_pushChar]
  exact AddMonoidHom.toMultiplicativeRight.apply_symm_apply _

theorem toMul_heckeT {A : Type} [AddCommGroup A] {L : ℕ} (K : Subgroup (ZMod L)ˣ) (ℓ : ℕ) [NeZero ℓ]
    (ψ : H1 L K A) :
    AddMonoidHom.toMultiplicativeRight (heckeT L K ℓ A ψ) =
      MonoidHom.transfer ((AddMonoidHom.toMultiplicativeRight ψ).comp (conjL L K ℓ)) :=
  AddMonoidHom.toMultiplicativeRight.apply_symm_apply _

variable (ℓ : ℕ) [NeZero ℓ]

include h in

theorem exists_compl (hℓ : Nat.Coprime ℓ (M' / (M * d))) :
    ∃ e : ℕ, M' = M * (d * e) ∧ Nat.Coprime ℓ e ∧ M ≠ 0 := by
  obtain ⟨e, he⟩ := h.exists_eq
  have hM : M ≠ 0 := by
    intro hM
    rw [hM, zero_mul] at he
    exact NeZero.ne M' he
  refine ⟨e, he, ?_, hM⟩
  have hMd : 0 < M * d := Nat.pos_of_ne_zero (mul_ne_zero hM (NeZero.ne d))
  have : M' / (M * d) = e := by
    rw [he, ← mul_assoc, Nat.mul_div_cancel_left e hMd]
  rwa [this] at hℓ

def lowerUnipotent (s : ℤ) : SL(2, ℤ) :=
  ⟨!![1, 0; (M' : ℤ) * s, 1], by rw [Matrix.det_fin_two_of]; ring⟩

theorem lowerUnipotent_mem (s : ℤ) : lowerUnipotent (M' := M') s ∈ GammaH M' H' := by
  have h0 : lowerUnipotent (M' := M') s ∈ Gamma0 M' := by
    rw [Gamma0_mem]
    show ((((!![1, 0; (M' : ℤ) * s, 1] : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod M') = 0)
    simp
  refine mem_GammaH_iff.mpr ⟨h0, ?_⟩
  have : gamma0Units M' ⟨_, h0⟩ = 1 := by
    ext
    simp only [val_gamma0Units, Gamma0Map, Units.val_one]
    show ((((!![1, 0; (M' : ℤ) * s, 1] : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod M') = 1)
    simp
  rw [this]
  exact one_mem H'

theorem exists_conjL_inv_mul_mem (hℓM : ℓ ∣ M) (hℓ : Nat.Coprime ℓ (M' / (M * d)))
    (g : ↥(GammaH M H)) :
    ∃ u : ↥(GammaHUpper M H ℓ), (conjL M H ℓ u)⁻¹ * g ∈ (iotaDeg M M' H H' d h).range := by
  obtain ⟨e, he, hcop, hM0⟩ := exists_compl h ℓ hℓ
  obtain ⟨hg0, hgu⟩ := mem_GammaH_iff.mp g.2
  have hdet := Matrix.SpecialLinearGroup.det_coe (g : SL(2, ℤ))
  rw [Matrix.det_fin_two] at hdet
  have hc : (M : ℤ) ∣ (g : SL(2, ℤ)) 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hg0)
  obtain ⟨c₁, hc₁⟩ := hc
  obtain ⟨m, hm⟩ := hℓM
  set D : ℤ := (g : SL(2, ℤ)) 1 1 with hD

  have hcopD : IsCoprime D (ℓ : ℤ) := by
    refine ⟨(g : SL(2, ℤ)) 0 0, -((g : SL(2, ℤ)) 0 1 * c₁ * m), ?_⟩
    have hMℓ : (M : ℤ) = ℓ * m := by rw [hm]; push_cast; ring
    rw [hc₁, hMℓ] at hdet
    linear_combination hdet
  have hcopE : IsCoprime (e : ℤ) (ℓ : ℤ) := (Nat.isCoprime_iff_coprime.mpr hcop).symm
  obtain ⟨a, b, hab⟩ := hcopD.mul_left hcopE

  set s : ℤ := -(c₁ * a) with hs
  set γ₀ : ↥(GammaH M' H') := ⟨lowerUnipotent (M' := M') s, lowerUnipotent_mem s⟩ with hγ₀
  set n₀ : ↥(GammaH M H) := iotaDeg M M' H H' d h γ₀ with hn₀
  have hd0 : (d : ℤ) ≠ 0 := by exact_mod_cast (NeZero.ne d)
  have hn₀00 : ((n₀ : ↥(GammaH M H)) : SL(2, ℤ)) 0 0 = 1 := by
    rw [hn₀, coe_iotaDeg, conjLowerMat_apply_00]; simp [hγ₀, lowerUnipotent]
  have hn₀01 : ((n₀ : ↥(GammaH M H)) : SL(2, ℤ)) 0 1 = 0 := by
    rw [hn₀, coe_iotaDeg, conjLowerMat_apply_01]; simp [hγ₀, lowerUnipotent]
  have hn₀10 : ((n₀ : ↥(GammaH M H)) : SL(2, ℤ)) 1 0 = (M : ℤ) * e * s := by
    rw [hn₀, coe_iotaDeg, conjLowerMat_apply_10]
    have : ((lowerUnipotent (M' := M') s : SL(2, ℤ)) 1 0) = (M' : ℤ) * s := by simp [lowerUnipotent]
    show ((lowerUnipotent (M' := M') s : SL(2, ℤ)) 1 0) / (d : ℤ) = (M : ℤ) * e * s
    rw [this, he]
    push_cast
    have : (M : ℤ) * (d * e) * s = (d : ℤ) * (M * e * s) := by ring
    rw [this, Int.mul_ediv_cancel_left _ hd0]
  have hn₀11 : ((n₀ : ↥(GammaH M H)) : SL(2, ℤ)) 1 1 = 1 := by
    rw [hn₀, coe_iotaDeg, conjLowerMat_apply_11]; simp [hγ₀, lowerUnipotent]

  set x : ↥(GammaH M H) := g * n₀ with hx
  have hx10 : ((x : ↥(GammaH M H)) : SL(2, ℤ)) 1 0 = (M : ℤ) * ℓ * (c₁ * b) := by
    rw [hx, Subgroup.coe_mul, SL2_mul_apply, hn₀00, hn₀10, hc₁, ← hD]
    have : (M : ℤ) * c₁ * 1 + D * ((M : ℤ) * e * s) = (M : ℤ) * (c₁ * (1 - a * (e * D))) := by
      rw [hs]; ring
    rw [this]
    have h1 : (1 : ℤ) - a * (e * D) = b * ℓ := by linear_combination (-1 : ℤ) * hab
    rw [h1]
    ring
  have hx11 : ((x : ↥(GammaH M H)) : SL(2, ℤ)) 1 1 = D := by
    rw [hx, Subgroup.coe_mul, SL2_mul_apply, hn₀01, hn₀11, ← hD]
    ring
  have hℓx : (ℓ : ℤ) ∣ ((x : ↥(GammaH M H)) : SL(2, ℤ)) 1 0 := by
    rw [hx10]; exact ⟨(M : ℤ) * (c₁ * b), by ring⟩

  set u₀ : SL(2, ℤ) := conjLowerMat ℓ ((x : ↥(GammaH M H)) : SL(2, ℤ)) hℓx with hu₀
  have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast (NeZero.ne ℓ)
  have hu₀0 : u₀ ∈ Gamma0 M := by
    rw [Gamma0_mem, hu₀, conjLowerMat_apply_10, hx10, ZMod.intCast_zmod_eq_zero_iff_dvd]
    refine ⟨c₁ * b, ?_⟩
    have : (M : ℤ) * ℓ * (c₁ * b) = ℓ * (M * (c₁ * b)) := by ring
    rw [this, Int.mul_ediv_cancel_left _ hℓ0]
  have hu₀H : u₀ ∈ GammaH M H :=
    mem_GammaH_of_entry_eq x.2 hu₀0 (by rw [hu₀, conjLowerMat_apply_11])
  have hu₀Up : (⟨u₀, hu₀H⟩ : ↥(GammaH M H)) ∈ GammaHUpper M H ℓ := by
    rw [Subgroup.mem_subgroupOf, mem_Gamma0Upper]
    show (((u₀ : SL(2, ℤ)) 0 1 : ℤ) : ZMod ℓ) = 0
    rw [hu₀, conjLowerMat_apply_01, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact dvd_mul_left _ _
  refine ⟨⟨⟨u₀, hu₀H⟩, hu₀Up⟩, ?_⟩

  have hcu : conjL M H ℓ ⟨⟨u₀, hu₀H⟩, hu₀Up⟩ = x := by
    apply Subtype.ext
    show conjUpperMat ℓ u₀ (dvd_of_mem_GammaHUpper M H ℓ ⟨⟨u₀, hu₀H⟩, hu₀Up⟩) =
      ((x : ↥(GammaH M H)) : SL(2, ℤ))
    exact conjUpperMat_conjLowerMat ℓ _ hℓx _
  rw [hcu, hx, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
  exact Subgroup.inv_mem _ ⟨γ₀, rfl⟩

theorem range_side (n : ↥((iotaDeg M M' H H' d h).range))
    (hn : (iotaInv h n : ↥(GammaH M' H')) ∈ GammaHUpper M' H' ℓ) :
    ∃ (hnUp : (n : ↥(GammaH M H)) ∈ GammaHUpper M H ℓ)
      (hcn : conjL M H ℓ ⟨n, hnUp⟩ ∈ (iotaDeg M M' H H' d h).range),
      iotaInv h ⟨conjL M H ℓ ⟨n, hnUp⟩, hcn⟩ = conjL M' H' ℓ ⟨iotaInv h n, hn⟩ := by
  set γ : ↥(GammaH M' H') := iotaInv h n with hγ
  have hγb : (ℓ : ℤ) ∣ (γ : SL(2, ℤ)) 0 1 := dvd_of_mem_GammaHUpper M' H' ℓ ⟨γ, hn⟩
  obtain ⟨e00, e01, e10, e11⟩ := iotaInv_entries h n
  have hnUp : (n : ↥(GammaH M H)) ∈ GammaHUpper M H ℓ := by
    rw [Subgroup.mem_subgroupOf, mem_Gamma0Upper, ZMod.intCast_zmod_eq_zero_iff_dvd, e01]
    exact Dvd.dvd.mul_right hγb _

  have key : conjL M H ℓ ⟨n, hnUp⟩ = iotaDeg M M' H H' d h (conjL M' H' ℓ ⟨γ, hn⟩) := by
    apply Subtype.ext
    have h₁ : (ℓ : ℤ) ∣ (conjLowerMat d (γ : SL(2, ℤ)) (h.dvd_entry γ)) 0 1 := by
      rw [conjLowerMat_apply_01]; exact Dvd.dvd.mul_right hγb _
    have h₂ : (d : ℤ) ∣ (conjUpperMat ℓ (γ : SL(2, ℤ)) hγb) 1 0 := by
      rw [conjUpperMat_apply_10]; exact Dvd.dvd.mul_right (h.dvd_entry γ) _
    calc ((conjL M H ℓ ⟨n, hnUp⟩ : ↥(GammaH M H)) : SL(2, ℤ))
        = conjUpperMat ℓ ((n : ↥(GammaH M H)) : SL(2, ℤ))
            (dvd_of_mem_GammaHUpper M H ℓ ⟨n, hnUp⟩) := rfl
      _ = conjUpperMat ℓ (conjLowerMat d (γ : SL(2, ℤ)) (h.dvd_entry γ)) h₁ :=
          conjUpperMat_congr ℓ (coe_iotaInv h n).symm _ _
      _ = conjLowerMat d (conjUpperMat ℓ (γ : SL(2, ℤ)) hγb) h₂ :=
          conjUpperMat_conjLowerMat_comm d ℓ _ _ _ h₁ h₂
      _ = ((iotaDeg M M' H H' d h (conjL M' H' ℓ ⟨γ, hn⟩) : ↥(GammaH M H)) : SL(2, ℤ)) := rfl
  have hcn : conjL M H ℓ ⟨n, hnUp⟩ ∈ (iotaDeg M M' H H' d h).range := by
    rw [key]; exact ⟨_, rfl⟩
  refine ⟨hnUp, hcn, ?_⟩
  have : (⟨conjL M H ℓ ⟨n, hnUp⟩, hcn⟩ : ↥((iotaDeg M M' H H' d h).range)) =
      ⟨iotaDeg M M' H H' d h (conjL M' H' ℓ ⟨γ, hn⟩), ⟨_, rfl⟩⟩ := Subtype.ext key
  rw [this, iotaInv_apply]

theorem upper_side (hℓ : Nat.Coprime ℓ (M' / (M * d))) (u : ↥(GammaHUpper M H ℓ))
    (hu : conjL M H ℓ u ∈ (iotaDeg M M' H H' d h).range) :
    ∃ huN : (u : ↥(GammaH M H)) ∈ (iotaDeg M M' H H' d h).range,
      (iotaInv h ⟨u, huN⟩ : ↥(GammaH M' H')) ∈ GammaHUpper M' H' ℓ := by
  obtain ⟨e, he, hcop, hM0⟩ := exists_compl h ℓ hℓ
  have hd0 : (d : ℤ) ≠ 0 := by exact_mod_cast (NeZero.ne d)
  have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast (NeZero.ne ℓ)
  set U : SL(2, ℤ) := ((u : ↥(GammaH M H)) : SL(2, ℤ)) with hU
  have hUb : (ℓ : ℤ) ∣ U 0 1 := dvd_of_mem_GammaHUpper M H ℓ u
  obtain ⟨hU0, hUu⟩ := mem_GammaH_iff.mp (u : ↥(GammaH M H)).2
  have hUc : (M : ℤ) ∣ U 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hU0)

  obtain ⟨hb, hmem⟩ := (mem_range_iotaDeg_iff h _).mp hu
  have hcoe : ((conjL M H ℓ u : ↥(GammaH M H)) : SL(2, ℤ)) = conjUpperMat ℓ U hUb := rfl
  rw [hcoe, conjUpperMat_apply_01] at hb

  obtain ⟨hγ0, hγu⟩ := mem_GammaH_iff.mp hmem
  have hM'c : (M' : ℤ) ∣ U 1 0 * ℓ * d := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hγ0)
    rwa [show ((conjUpperMat d ((conjL M H ℓ u : ↥(GammaH M H)) : SL(2, ℤ)) _) 1 0) = U 1 0 * ℓ * d
      from by rw [conjUpperMat_apply_10, hcoe, conjUpperMat_apply_10]] at this

  obtain ⟨v, hv⟩ := hUc
  have hev : (e : ℤ) ∣ v := by
    have h1 : (M : ℤ) * (d * e) ∣ (M : ℤ) * d * (v * ℓ) := by
      have : U 1 0 * ℓ * d = (M : ℤ) * d * (v * ℓ) := by rw [hv]; ring
      rw [← this]; exact_mod_cast (he ▸ hM'c)
    have hMd : (M : ℤ) * d ≠ 0 := mul_ne_zero (by exact_mod_cast hM0) hd0
    have h2 : (e : ℤ) ∣ v * ℓ := by
      rw [show (M : ℤ) * (d * e) = (M : ℤ) * d * e from by ring] at h1
      exact (mul_dvd_mul_iff_left hMd).mp h1
    exact (Nat.isCoprime_iff_coprime.mpr hcop).symm.dvd_of_dvd_mul_right h2
  have hM'Ud : (M' : ℤ) ∣ U 1 0 * d := by
    obtain ⟨w, hw⟩ := hev
    rw [hv, hw, he]
    push_cast
    exact ⟨w, by ring⟩

  have hdU : (d : ℤ) ∣ U 0 1 := by
    obtain ⟨w, hw⟩ := hb
    refine ⟨ℓ * w, ?_⟩
    calc U 0 1 = ℓ * (U 0 1 / ℓ) := (Int.mul_ediv_cancel' hUb).symm
      _ = ℓ * (d * w) := by rw [hw]
      _ = d * (ℓ * w) := by ring
  have hγ'0 : conjUpperMat d U hdU ∈ Gamma0 M' := by
    rw [Gamma0_mem, conjUpperMat_apply_10, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hM'Ud
  have hγ'H : conjUpperMat d U hdU ∈ GammaH M' H' :=
    mem_GammaH_of_entry_eq hmem hγ'0
      (by rw [conjUpperMat_apply_11, conjUpperMat_apply_11, hcoe, conjUpperMat_apply_11])
  have huN : (u : ↥(GammaH M H)) ∈ (iotaDeg M M' H H' d h).range :=
    (mem_range_iotaDeg_iff h _).mpr ⟨hdU, hγ'H⟩
  refine ⟨huN, ?_⟩

  have hinv : iotaInv h ⟨u, huN⟩ = ⟨conjUpperMat d U hdU, hγ'H⟩ := by
    have hι : iotaDeg M M' H H' d h ⟨conjUpperMat d U hdU, hγ'H⟩ = (u : ↥(GammaH M H)) := by
      apply Subtype.ext
      rw [coe_iotaDeg]
      exact conjLowerMat_conjUpperMat d U hdU _
    have : (⟨(u : ↥(GammaH M H)), huN⟩ : ↥((iotaDeg M M' H H' d h).range)) =
        ⟨iotaDeg M M' H H' d h ⟨conjUpperMat d U hdU, hγ'H⟩, ⟨_, rfl⟩⟩ := Subtype.ext hι.symm
    rw [this, iotaInv_apply]
  rw [hinv, Subgroup.mem_subgroupOf, mem_Gamma0Upper, ZMod.intCast_zmod_eq_zero_iff_dvd]
  show (ℓ : ℤ) ∣ (conjUpperMat d U hdU) 0 1
  rw [conjUpperMat_apply_01]
  obtain ⟨w, hw⟩ := hb
  refine ⟨w, ?_⟩
  have hU01 : U 0 1 = d * (ℓ * w) := by
    calc U 0 1 = ℓ * (U 0 1 / ℓ) := (Int.mul_ediv_cancel' hUb).symm
      _ = ℓ * (d * w) := by rw [hw]
      _ = d * (ℓ * w) := by ring
  rw [hU01, Int.mul_ediv_cancel_left _ hd0]

theorem subgroups_eq (hℓ : Nat.Coprime ℓ (M' / (M * d))) :
    (((iotaDeg M M' H H' d h).range.comap (conjL M H ℓ)).map (GammaHUpper M H ℓ).subtype) =
      (((GammaHUpper M' H' ℓ).comap (iotaInv h).toMonoidHom).map
        (iotaDeg M M' H H' d h).range.subtype) := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_comap, Subgroup.coe_subtype]
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨huN, hup⟩ := upper_side h ℓ hℓ u hu
    exact ⟨⟨u, huN⟩, hup, rfl⟩
  · rintro ⟨n, hn, rfl⟩
    rw [MulEquiv.coe_toMonoidHom] at hn
    obtain ⟨hnUp, hcn, -⟩ := range_side h ℓ n hn
    exact ⟨⟨n, hnUp⟩, hcn, rfl⟩

theorem chars_agree (u : ↥(GammaHUpper M H ℓ)) (hu : conjL M H ℓ u ∈ (iotaDeg M M' H H' d h).range)
    (huN : (u : ↥(GammaH M H)) ∈ (iotaDeg M M' H H' d h).range)
    (hn : (iotaInv h ⟨u, huN⟩ : ↥(GammaH M' H')) ∈ GammaHUpper M' H' ℓ) :
    iotaInv h ⟨conjL M H ℓ u, hu⟩ = conjL M' H' ℓ ⟨iotaInv h ⟨u, huN⟩, hn⟩ := by
  obtain ⟨hnUp, hcn, key⟩ := range_side h ℓ ⟨u, huN⟩ hn
  exact key

end Level

section Assembly

open CohCarrier CongruenceSubgroup
open scoped MatrixGroups

variable {M M' : ℕ} {H : Subgroup (ZMod M)ˣ} {H' : Subgroup (ZMod M')ˣ} {d ℓ : ℕ} {A : Type}
  [AddCommGroup A] [NeZero d] [NeZero M'] [NeZero ℓ]

theorem main (h : LevelLE M M' H H' d) (hℓ : Nat.Coprime ℓ (M' / (M * d))) (hℓM : ℓ ∣ M)
    (φ : H1 M' H' A) :
    heckeT M H ℓ A (jDeg M M' H H' d A h φ) = jDeg M M' H H' d A h (heckeT M' H' ℓ A φ) := by
  apply AddMonoidHom.toMultiplicativeRight.injective
  rw [toMul_heckeT, toMul_jDeg, toMul_jDeg, toMul_heckeT]

  set N : Subgroup ↥(GammaH M H) := (iotaDeg M M' H H' d h).range with hN
  set ιinv : ↥N →* ↥(GammaH M' H') := (iotaInv h).toMonoidHom with hιinv
  set cb : ↥(GammaHUpper M H ℓ) →* ↥(GammaH M H) := conjL M H ℓ with hcb
  set cs : ↥(GammaHUpper M' H' ℓ) →* ↥(GammaH M' H') := conjL M' H' ℓ with hcs
  set χ : ↥(GammaH M' H') →* Multiplicative A := AddMonoidHom.toMultiplicativeRight φ with hχ

  have hsupp : ∀ g : ↥(GammaH M H), ∃ u : ↥(GammaHUpper M H ℓ), (cb u)⁻¹ * g ∈ N :=
    exists_conjL_inv_mul_mem h ℓ hℓM hℓ
  have hsupp' : ∀ y : ↥(GammaH M' H'), ∃ n : ↥N, (ιinv n)⁻¹ * y ∈ GammaHUpper M' H' ℓ := by
    intro y
    refine ⟨⟨iotaDeg M M' H H' d h y, ⟨y, rfl⟩⟩, ?_⟩
    rw [hιinv, MulEquiv.coe_toMonoidHom, iotaInv_apply, inv_mul_cancel]
    exact one_mem _
  haveI hfi1 : (N.comap cb).FiniteIndex := finiteIndex_comap_of_forall_exists cb N hsupp
  haveI hfi2 : ((GammaHUpper M' H' ℓ).comap ιinv).FiniteIndex :=
    finiteIndex_comap_of_forall_exists ιinv _ hsupp'
  haveI hfi3 : ((N.comap cb).map (GammaHUpper M H ℓ).subtype).FiniteIndex :=
    finiteIndex_map_subtype _ _
  haveI hfi4 : (((GammaHUpper M' H' ℓ).comap ιinv).map N.subtype).FiniteIndex :=
    finiteIndex_map_subtype _ _
  refine MonoidHom.ext fun g => ?_

  have hL1 : (MonoidHom.transfer (χ.comp ιinv)).comp cb =
      MonoidHom.transfer ((χ.comp ιinv).comp (cb.subgroupComap N)) :=
    MonoidHom.ext fun u => transfer_apply_eq_transfer_comap cb N hsupp _ u
  have hR1 : (MonoidHom.transfer (χ.comp cs)).comp ιinv =
      MonoidHom.transfer ((χ.comp cs).comp (ιinv.subgroupComap (GammaHUpper M' H' ℓ))) :=
    MonoidHom.ext fun n => transfer_apply_eq_transfer_comap ιinv _ hsupp' _ n
  rw [hL1, hR1, transfer_transfer_apply, transfer_transfer_apply]
  refine transfer_congr_of_eq (subgroups_eq h ℓ hℓ) _ _ (fun x h₁ h₂ => ?_) g

  obtain ⟨u, hu, hux⟩ := Subgroup.mem_map.mp h₁
  obtain ⟨n, hn, hnx⟩ := Subgroup.mem_map.mp h₂
  rw [Subgroup.mem_comap] at hu hn
  subst hux
  have huN : ((u : ↥(GammaH M H))) ∈ N := by
    have hn2 := n.2
    rw [show ((n : ↥(GammaH M H))) = u from hnx] at hn2
    exact hn2
  have hnu : n = ⟨u, huN⟩ := Subtype.ext hnx
  subst hnu
  have E1 : pushSubtype (GammaHUpper M H ℓ) (N.comap cb) ((χ.comp ιinv).comp (cb.subgroupComap N))
      ⟨(GammaHUpper M H ℓ).subtype u, h₁⟩ = ((χ.comp ιinv).comp (cb.subgroupComap N)) ⟨u, hu⟩ :=
    pushSubtype_apply _ _ _ ⟨u, hu⟩ h₁
  have E2 : pushSubtype N ((GammaHUpper M' H' ℓ).comap ιinv)
      ((χ.comp cs).comp (ιinv.subgroupComap (GammaHUpper M' H' ℓ)))
      ⟨(GammaHUpper M H ℓ).subtype u, h₂⟩ =
      ((χ.comp cs).comp (ιinv.subgroupComap (GammaHUpper M' H' ℓ))) ⟨⟨u, huN⟩, hn⟩ :=
    pushSubtype_apply N ((GammaHUpper M' H' ℓ).comap ιinv) _
      ⟨⟨(u : ↥(GammaH M H)), huN⟩, hn⟩ h₂
  refine E1.trans (Eq.trans ?_ E2.symm)
  show χ (iotaInv h ⟨conjL M H ℓ u, hu⟩) = χ (conjL M' H' ℓ ⟨iotaInv h ⟨u, huN⟩, hn⟩)
  rw [chars_agree h ℓ u hu huN hn]

end Assembly

end JDegHeckeUCoprimeSol
p2m_reactivate "P2MW.S_CohCarrier_jDeg_heckeT_comm_of_dvd_of_coprime.JDegHeckeUCoprimeSol"

theorem solution {M M' : ℕ} {H : Subgroup (ZMod M)ˣ} {H' : Subgroup (ZMod M')ˣ} {d ℓ : ℕ}
    {A : Type} [AddCommGroup A] [NeZero d] [NeZero M'] [NeZero ℓ]
    (h : CohCarrier.LevelLE M M' H H' d) (hℓe : Nat.Coprime ℓ (M' / (M * d))) (hℓM : ℓ ∣ M)
    (φ : CohCarrier.H1 M' H' A) :
    CohCarrier.heckeT M H ℓ A (CohCarrier.jDeg M M' H H' d A h φ)
      = CohCarrier.jDeg M M' H H' d A h (CohCarrier.heckeT M' H' ℓ A φ) :=
  JDegHeckeUCoprimeSol.main h hℓe hℓM φ

end S_CohCarrier_jDeg_heckeT_comm_of_dvd_of_coprime
end P2MW
export P2MW.S_CohCarrier_jDeg_heckeT_comm_of_dvd_of_coprime (solution)
