-- Prove2me | solution 1 for CohCarrier.jDeg_heckeT_comm_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/e47c8b8c-1ca0-56dd-ba0b-318f21117767

import Mathlib
import Definitions.Def_CohCarrier_Level
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_jDeg_heckeT_comm_of_dvd

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

namespace JDegHeckeUSol

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

section Level

open CohCarrier CongruenceSubgroup
open scoped MatrixGroups

variable {M : ℕ} {H H' : Subgroup (ZMod M)ˣ} [NeZero M]

theorem conjLowerMat_one (A : SL(2, ℤ)) (hA : ((1 : ℕ) : ℤ) ∣ A 1 0) :
    conjLowerMat 1 A hA = A := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [conjLowerMat]

theorem gamma0Units_eq_of_entry_eq (x y : ↥(Gamma0 M))
    (hxy : (x : SL(2, ℤ)) 1 1 = (y : SL(2, ℤ)) 1 1) : gamma0Units M x = gamma0Units M y := by
  ext
  simp only [val_gamma0Units]
  show (((x : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) = (((y : SL(2, ℤ)) 1 1 : ℤ) : ZMod M)
  rw [hxy]

theorem gamma0Units_mem_of_mem {K : Subgroup (ZMod M)ˣ} {x : SL(2, ℤ)} (hx : x ∈ GammaH M K)
    (hx0 : x ∈ Gamma0 M) : gamma0Units M ⟨x, hx0⟩ ∈ K := by
  obtain ⟨_, hu⟩ := mem_GammaH_iff.mp hx
  exact hu

variable (h : LevelLE M M H H' 1)

theorem coe_iotaDeg_one (γ : ↥(GammaH M H')) :
    ((iotaDeg M M H H' 1 h γ : ↥(GammaH M H)) : SL(2, ℤ)) = γ :=
  conjLowerMat_one _ (h.dvd_entry γ)

theorem mem_range_iotaDeg_one_iff (x : ↥(GammaH M H)) :
    x ∈ (iotaDeg M M H H' 1 h).range ↔ (x : SL(2, ℤ)) ∈ GammaH M H' := by
  constructor
  · rintro ⟨γ, rfl⟩
    rw [coe_iotaDeg_one]
    exact γ.2
  · intro hx
    exact ⟨⟨x, hx⟩, Subtype.ext (coe_iotaDeg_one h ⟨x, hx⟩)⟩

noncomputable def iotaInv : ↥((iotaDeg M M H H' 1 h).range) ≃* ↥(GammaH M H') :=
  (MonoidHom.ofInjective (iotaDeg_injective M M H H' 1 h)).symm

theorem iotaInv_apply (γ : ↥(GammaH M H')) (hγ : iotaDeg M M H H' 1 h γ ∈ (iotaDeg M M H H' 1 h).range) :
    iotaInv h ⟨iotaDeg M M H H' 1 h γ, hγ⟩ = γ := by
  have : (⟨iotaDeg M M H H' 1 h γ, hγ⟩ : ↥((iotaDeg M M H H' 1 h).range)) =
      MonoidHom.ofInjective (iotaDeg_injective M M H H' 1 h) γ := Subtype.ext rfl
  rw [this, iotaInv, MulEquiv.symm_apply_apply]

theorem coe_iotaInv (n : ↥((iotaDeg M M H H' 1 h).range)) :
    ((iotaInv h n : ↥(GammaH M H')) : SL(2, ℤ)) = ((n : ↥(GammaH M H)) : SL(2, ℤ)) := by
  have e := MonoidHom.apply_ofInjective_symm (iotaDeg_injective M M H H' 1 h) n
  rw [← coe_iotaDeg_one h (iotaInv h n)]
  exact congrArg Subtype.val e

theorem toMul_pushChar {A : Type} [AddCommGroup A] (ψ : H1 M H' A) :
    AddMonoidHom.toMultiplicativeRight (pushChar M M H H' 1 A h ψ) =
      (AddMonoidHom.toMultiplicativeRight ψ).comp (iotaInv h).toMonoidHom :=
  MonoidHom.ext fun _ => rfl

theorem toMul_jDeg {A : Type} [AddCommGroup A] (ψ : H1 M H' A) :
    AddMonoidHom.toMultiplicativeRight (jDeg M M H H' 1 A h ψ) =
      MonoidHom.transfer ((AddMonoidHom.toMultiplicativeRight ψ).comp (iotaInv h).toMonoidHom) := by
  rw [← toMul_pushChar]
  exact AddMonoidHom.toMultiplicativeRight.apply_symm_apply _

theorem toMul_heckeT {A : Type} [AddCommGroup A] (K : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ]
    (ψ : H1 M K A) :
    AddMonoidHom.toMultiplicativeRight (heckeT M K ℓ A ψ) =
      MonoidHom.transfer ((AddMonoidHom.toMultiplicativeRight ψ).comp (conjL M K ℓ)) :=
  AddMonoidHom.toMultiplicativeRight.apply_symm_apply _

variable (ℓ : ℕ) [NeZero ℓ]

theorem conjL_mem_range_iff (u : ↥(GammaHUpper M H ℓ)) :
    conjL M H ℓ u ∈ (iotaDeg M M H H' 1 h).range ↔
      (((u : ↥(GammaH M H)) : SL(2, ℤ)) ∈ GammaH M H') := by
  rw [mem_range_iotaDeg_one_iff]
  have hc0 : ((conjL M H ℓ u : ↥(GammaH M H)) : SL(2, ℤ)) ∈ Gamma0 M :=
    GammaH_le_Gamma0 H (conjL M H ℓ u).2
  have hu0 : (((u : ↥(GammaH M H)) : SL(2, ℤ))) ∈ Gamma0 M :=
    GammaH_le_Gamma0 H (u : ↥(GammaH M H)).2
  have hunits : gamma0Units M ⟨_, hc0⟩ = gamma0Units M ⟨_, hu0⟩ :=
    gamma0Units_eq_of_entry_eq _ _ (conjUpperMat_apply_11 ℓ _ (dvd_of_mem_GammaHUpper M H ℓ u))
  constructor
  · intro hmem
    exact mem_GammaH_iff.mpr ⟨hu0, hunits ▸ gamma0Units_mem_of_mem hmem hc0⟩
  · intro hmem
    exact mem_GammaH_iff.mpr ⟨hc0, hunits.symm ▸ gamma0Units_mem_of_mem hmem hu0⟩

theorem exists_conjL_inv_mul_mem (hℓM : ℓ ∣ M) (g : ↥(GammaH M H)) :
    ∃ u : ↥(GammaHUpper M H ℓ), (conjL M H ℓ u)⁻¹ * g ∈ (iotaDeg M M H H' 1 h).range := by
  obtain ⟨hg0, hgu⟩ := mem_GammaH_iff.mp g.2
  have hdet := Matrix.SpecialLinearGroup.det_coe (g : SL(2, ℤ))
  rw [Matrix.det_fin_two] at hdet
  have hc : (M : ℤ) ∣ (g : SL(2, ℤ)) 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hg0)
  obtain ⟨c₁, hc₁⟩ := hc
  obtain ⟨m, hm⟩ := hℓM
  set d : ℤ := (g : SL(2, ℤ)) 1 1 with hd
  have hcop : IsCoprime d ((ℓ : ℤ) * M) := by
    have h1 : IsCoprime d (M : ℤ) := by
      refine ⟨(g : SL(2, ℤ)) 0 0, -((g : SL(2, ℤ)) 0 1 * c₁), ?_⟩
      rw [hc₁] at hdet
      linear_combination hdet
    have h2 : IsCoprime d ((ℓ : ℤ) * M * m) := by
      have hMM : (ℓ : ℤ) * M * m = (M : ℤ) * M := by rw [hm]; push_cast; ring
      rw [hMM]
      exact h1.mul_right h1
    exact h2.of_mul_right_left
  obtain ⟨a, k, hak⟩ := hcop
  let u₀ : SL(2, ℤ) := ⟨!![a, -k * ℓ; (M : ℤ), d], by
    rw [Matrix.det_fin_two_of]
    linear_combination hak⟩
  have hu0 : u₀ ∈ Gamma0 M := by
    rw [Gamma0_mem]
    simp [u₀]
  have hu11 : (u₀ : SL(2, ℤ)) 1 1 = (g : SL(2, ℤ)) 1 1 := by simp [u₀, hd]
  have huH : u₀ ∈ GammaH M H := by
    rw [mem_GammaH_iff]
    refine ⟨hu0, ?_⟩
    rw [gamma0Units_eq_of_entry_eq ⟨u₀, hu0⟩ ⟨g, hg0⟩ hu11]
    exact hgu
  have huUp : (⟨u₀, huH⟩ : ↥(GammaH M H)) ∈ GammaHUpper M H ℓ := by
    rw [Subgroup.mem_subgroupOf, mem_Gamma0Upper]
    show (((!![a, -k * ℓ; (M : ℤ), d] : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℤ) : ZMod ℓ) = 0
    simp
  refine ⟨⟨⟨u₀, huH⟩, huUp⟩, ?_⟩
  rw [mem_range_iotaDeg_one_iff]
  set c := conjL M H ℓ ⟨⟨u₀, huH⟩, huUp⟩ with hcdef
  have hc0 : ((c : ↥(GammaH M H)) : SL(2, ℤ)) ∈ Gamma0 M := GammaH_le_Gamma0 H c.2
  have hx0 : (((c⁻¹ * g : ↥(GammaH M H))) : SL(2, ℤ)) ∈ Gamma0 M := GammaH_le_Gamma0 H (c⁻¹ * g).2
  refine mem_GammaH_iff.mpr ⟨hx0, ?_⟩
  have hprod : (⟨((c⁻¹ * g : ↥(GammaH M H)) : SL(2, ℤ)), hx0⟩ : ↥(Gamma0 M)) =
      (⟨(c : SL(2, ℤ)), hc0⟩ : ↥(Gamma0 M))⁻¹ * ⟨g, hg0⟩ := Subtype.ext rfl
  have hcu : gamma0Units M ⟨(c : SL(2, ℤ)), hc0⟩ = gamma0Units M ⟨g, hg0⟩ :=
    gamma0Units_eq_of_entry_eq _ _
      ((conjUpperMat_apply_11 ℓ u₀ (dvd_of_mem_GammaHUpper M H ℓ ⟨⟨u₀, huH⟩, huUp⟩)).trans hu11)
  rw [hprod, map_mul, map_inv, hcu, inv_mul_cancel]
  exact one_mem H'

theorem subgroups_eq :
    (((iotaDeg M M H H' 1 h).range.comap (conjL M H ℓ)).map (GammaHUpper M H ℓ).subtype) =
      (((GammaHUpper M H' ℓ).comap (iotaInv h).toMonoidHom).map
        (iotaDeg M M H H' 1 h).range.subtype) := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_comap, Subgroup.coe_subtype]
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hx' : ((u : ↥(GammaH M H)) : SL(2, ℤ)) ∈ GammaH M H' := (conjL_mem_range_iff h ℓ u).mp hu
    have hxN : (u : ↥(GammaH M H)) ∈ (iotaDeg M M H H' 1 h).range :=
      (mem_range_iotaDeg_one_iff h _).mpr hx'
    refine ⟨⟨u, hxN⟩, ?_, rfl⟩
    show (iotaInv h ⟨u, hxN⟩ : ↥(GammaH M H')) ∈ GammaHUpper M H' ℓ
    rw [Subgroup.mem_subgroupOf, coe_iotaInv]
    exact Subgroup.mem_subgroupOf.mp u.2
  · rintro ⟨n, hn, rfl⟩
    have hnUp : (n : ↥(GammaH M H)) ∈ GammaHUpper M H ℓ := by
      rw [Subgroup.mem_subgroupOf]
      have := Subgroup.mem_subgroupOf.mp hn
      rwa [MulEquiv.coe_toMonoidHom, coe_iotaInv] at this
    refine ⟨⟨n, hnUp⟩, ?_, rfl⟩
    rw [conjL_mem_range_iff]
    exact (mem_range_iotaDeg_one_iff h _).mp n.2

theorem conjUpperMat_congr {A B : SL(2, ℤ)} (hAB : A = B) (hA : (ℓ : ℤ) ∣ A 0 1) (hB : (ℓ : ℤ) ∣ B 0 1) :
    conjUpperMat ℓ A hA = conjUpperMat ℓ B hB := by
  subst hAB
  rfl

theorem chars_agree {A : Type} [AddCommGroup A] (φ : H1 M H' A)
    (u : ↥(GammaHUpper M H ℓ)) (hu : conjL M H ℓ u ∈ (iotaDeg M M H H' 1 h).range)
    (n : ↥((iotaDeg M M H H' 1 h).range)) (hn : (iotaInv h n : ↥(GammaH M H')) ∈ GammaHUpper M H' ℓ)
    (hun : ((u : ↥(GammaH M H)) : SL(2, ℤ)) = ((n : ↥(GammaH M H)) : SL(2, ℤ))) :
    iotaInv h ⟨conjL M H ℓ u, hu⟩ = conjL M H' ℓ ⟨iotaInv h n, hn⟩ := by
  apply Subtype.ext
  rw [coe_iotaInv]
  exact conjUpperMat_congr ℓ (hun.trans (coe_iotaInv h n).symm) (dvd_of_mem_GammaHUpper M H ℓ u)
    (dvd_of_mem_GammaHUpper M H' ℓ ⟨iotaInv h n, hn⟩)

end Level

section Assembly

open CohCarrier CongruenceSubgroup
open scoped MatrixGroups

variable {M : ℕ} {H H' : Subgroup (ZMod M)ˣ} {ℓ : ℕ} {A : Type} [AddCommGroup A]
  [NeZero M] [NeZero ℓ]

theorem main (h : LevelLE M M H H' 1) (hℓM : ℓ ∣ M) (φ : H1 M H' A) :
    heckeT M H ℓ A (jDeg M M H H' 1 A h φ) = jDeg M M H H' 1 A h (heckeT M H' ℓ A φ) := by
  apply AddMonoidHom.toMultiplicativeRight.injective
  rw [toMul_heckeT, toMul_jDeg, toMul_jDeg, toMul_heckeT]

  set N : Subgroup ↥(GammaH M H) := (iotaDeg M M H H' 1 h).range with hN
  set ιinv : ↥N →* ↥(GammaH M H') := (iotaInv h).toMonoidHom with hιinv
  set cb : ↥(GammaHUpper M H ℓ) →* ↥(GammaH M H) := conjL M H ℓ with hcb
  set cs : ↥(GammaHUpper M H' ℓ) →* ↥(GammaH M H') := conjL M H' ℓ with hcs
  set χ : ↥(GammaH M H') →* Multiplicative A := AddMonoidHom.toMultiplicativeRight φ with hχ

  have hsupp : ∀ g : ↥(GammaH M H), ∃ u : ↥(GammaHUpper M H ℓ), (cb u)⁻¹ * g ∈ N :=
    exists_conjL_inv_mul_mem h ℓ hℓM
  have hsupp' : ∀ y : ↥(GammaH M H'), ∃ n : ↥N, (ιinv n)⁻¹ * y ∈ GammaHUpper M H' ℓ := by
    intro y
    refine ⟨⟨iotaDeg M M H H' 1 h y, ⟨y, rfl⟩⟩, ?_⟩
    rw [hιinv, MulEquiv.coe_toMonoidHom, iotaInv_apply, inv_mul_cancel]
    exact one_mem _
  haveI hfi1 : (N.comap cb).FiniteIndex := finiteIndex_comap_of_forall_exists cb N hsupp
  haveI hfi2 : ((GammaHUpper M H' ℓ).comap ιinv).FiniteIndex :=
    finiteIndex_comap_of_forall_exists ιinv _ hsupp'
  haveI hfi3 : ((N.comap cb).map (GammaHUpper M H ℓ).subtype).FiniteIndex :=
    finiteIndex_map_subtype _ _
  haveI hfi4 : (((GammaHUpper M H' ℓ).comap ιinv).map N.subtype).FiniteIndex :=
    finiteIndex_map_subtype _ _
  refine MonoidHom.ext fun g => ?_

  have hL1 : (MonoidHom.transfer (χ.comp ιinv)).comp cb =
      MonoidHom.transfer ((χ.comp ιinv).comp (cb.subgroupComap N)) :=
    MonoidHom.ext fun u => transfer_apply_eq_transfer_comap cb N hsupp _ u
  have hR1 : (MonoidHom.transfer (χ.comp cs)).comp ιinv =
      MonoidHom.transfer ((χ.comp cs).comp (ιinv.subgroupComap (GammaHUpper M H' ℓ))) :=
    MonoidHom.ext fun n => transfer_apply_eq_transfer_comap ιinv _ hsupp' _ n
  rw [hL1, hR1, transfer_transfer_apply, transfer_transfer_apply]
  refine transfer_congr_of_eq (subgroups_eq h ℓ) _ _ (fun x h₁ h₂ => ?_) g

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
  have E2 : pushSubtype N ((GammaHUpper M H' ℓ).comap ιinv)
      ((χ.comp cs).comp (ιinv.subgroupComap (GammaHUpper M H' ℓ)))
      ⟨(GammaHUpper M H ℓ).subtype u, h₂⟩ =
      ((χ.comp cs).comp (ιinv.subgroupComap (GammaHUpper M H' ℓ))) ⟨⟨u, huN⟩, hn⟩ :=
    pushSubtype_apply N ((GammaHUpper M H' ℓ).comap ιinv) _
      ⟨⟨(u : ↥(GammaH M H)), huN⟩, hn⟩ h₂
  refine E1.trans (Eq.trans ?_ E2.symm)
  show χ (iotaInv h ⟨conjL M H ℓ u, hu⟩) = χ (conjL M H' ℓ ⟨iotaInv h ⟨u, huN⟩, hn⟩)
  rw [chars_agree h ℓ φ u hu ⟨u, huN⟩ hn rfl]

end Assembly

end JDegHeckeUSol

theorem solution {M : ℕ} {H H' : Subgroup (ZMod M)ˣ} {ℓ : ℕ}
    {A : Type} [AddCommGroup A] [NeZero M] [NeZero ℓ]
    (h : CohCarrier.LevelLE M M H H' 1) (hℓM : ℓ ∣ M) (φ : CohCarrier.H1 M H' A) :
    CohCarrier.heckeT M H ℓ A (CohCarrier.jDeg M M H H' 1 A h φ) =
      CohCarrier.jDeg M M H H' 1 A h (CohCarrier.heckeT M H' ℓ A φ) :=
  JDegHeckeUSol.main h hℓM φ

end S_CohCarrier_jDeg_heckeT_comm_of_dvd
end P2MW
export P2MW.S_CohCarrier_jDeg_heckeT_comm_of_dvd (solution)
