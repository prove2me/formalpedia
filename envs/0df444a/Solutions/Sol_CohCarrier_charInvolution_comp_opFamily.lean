-- Prove2me | solution 1 for CohCarrier.charInvolution_comp_opFamily
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/1383174a-98ac-565a-963b-7cf282440d65

import Mathlib
import Definitions.Def_CohCarrier_Inst
import Definitions.Def_CohCarrier_CharInvolution
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_charInvolution_comp_opFamily

set_option autoImplicit false

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

namespace CharInvHecke

section TransferNat

variable {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
  (K : Subgroup G) (K' : Subgroup G') (hK : ∀ x, e x ∈ K' ↔ x ∈ K)

def resK : K →* K' where
  toFun x := ⟨e x, (hK x).mpr x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)

@[scoped simp] theorem coe_resK (x : K) : ((resK e K K' hK x : K') : G') = e x := rfl

def quotEquiv : G ⧸ K ≃ G' ⧸ K' :=
  Quotient.congr e.toEquiv fun a b => by
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, ← hK, map_mul, map_inv]
    rfl

theorem quotEquiv_mk (x : G) :
    quotEquiv e K K' hK (QuotientGroup.mk x) = QuotientGroup.mk (e x) := rfl

theorem quotEquiv_smul (g : G) (q : G ⧸ K) :
    quotEquiv e K K' hK (g • q) = e g • quotEquiv e K K' hK q := by
  induction q using QuotientGroup.induction_on with
  | H x =>
    rw [MulAction.Quotient.smul_mk, quotEquiv_mk, quotEquiv_mk, MulAction.Quotient.smul_mk, smul_eq_mul,
      smul_eq_mul, map_mul]

variable {C : Type*} [CommGroup C]

theorem transfer_comp_resK [K.FiniteIndex] [K'.FiniteIndex] (ψ : K' →* C) (g : G) :
    MonoidHom.transfer (ψ.comp (resK e K K' hK)) g = MonoidHom.transfer ψ (e g) := by
  classical
  letI := K.fintypeQuotientOfFiniteIndex
  letI := K'.fintypeQuotientOfFiniteIndex

  set f : G ⧸ K → G := Quotient.out with hfdef
  have hf : ∀ q, (f q : G ⧸ K) = q := fun q => Quotient.out_eq q
  set ē := quotEquiv e K K' hK with hē
  set f' : G' ⧸ K' → G' := fun q' => e (f (ē.symm q')) with hf'def
  have hf' : ∀ q', (f' q' : G' ⧸ K') = q' := by
    intro q'
    show QuotientGroup.mk (e (f (ē.symm q'))) = q'
    rw [← quotEquiv_mk e K K' hK, hf, ← hē, Equiv.apply_symm_apply]
  let T : K.LeftTransversal := ⟨Set.range f, Subgroup.isComplement_range_left hf⟩
  let T' : K'.LeftTransversal := ⟨Set.range f', Subgroup.isComplement_range_left hf'⟩
  rw [MonoidHom.transfer_def _ T g, MonoidHom.transfer_def _ T' (e g)]
  simp only [Subgroup.leftTransversals.diff]
  refine Fintype.prod_equiv ē _ _ fun x => ?_
  rw [MonoidHom.comp_apply]
  congr 1
  apply Subtype.ext
  show e ((T.2.leftQuotientEquiv x : G)⁻¹ * ((g • T).2.leftQuotientEquiv x : G)) =
    (T'.2.leftQuotientEquiv (ē x) : G')⁻¹ * ((e g • T').2.leftQuotientEquiv (ē x) : G')
  rw [map_mul, map_inv, Subgroup.smul_apply_eq_smul_apply_inv_smul,
    Subgroup.smul_apply_eq_smul_apply_inv_smul]
  have e1 : (T.2.leftQuotientEquiv x : G) = f x := Subgroup.IsComplement.leftQuotientEquiv_apply hf x
  have e2 : (T.2.leftQuotientEquiv (g⁻¹ • x) : G) = f (g⁻¹ • x) := Subgroup.IsComplement.leftQuotientEquiv_apply hf _
  have e3 : (T'.2.leftQuotientEquiv (ē x) : G') = f' (ē x) := Subgroup.IsComplement.leftQuotientEquiv_apply hf' _
  have e4 : (T'.2.leftQuotientEquiv ((e g)⁻¹ • ē x) : G') = f' ((e g)⁻¹ • ē x) :=
    Subgroup.IsComplement.leftQuotientEquiv_apply hf' _
  rw [e1, e2, e3, e4]
  have hsm : (e g)⁻¹ • ē x = ē (g⁻¹ • x) := by rw [hē, quotEquiv_smul, map_inv]
  rw [hsm, hf'def]
  simp only [Equiv.symm_apply_apply, smul_eq_mul, map_mul]

end TransferNat

section JConj

open CohCarrier

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ)

def jEquiv : ↥(GammaH M H) ≃* ↥(GammaH M H) :=
  { jConjGammaH M H with
    invFun := jConjGammaH M H
    left_inv := jConjGammaH_jConjGammaH M H
    right_inv := jConjGammaH_jConjGammaH M H }

@[scoped simp] theorem jEquiv_apply (γ : ↥(GammaH M H)) : jEquiv M H γ = jConjGammaH M H γ := rfl

theorem jEquiv_mem_upper_iff (γ : ↥(GammaH M H)) :
    jEquiv M H γ ∈ GammaHUpper M H ℓ ↔ γ ∈ GammaHUpper M H ℓ := by
  rw [GammaHUpper, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, mem_Gamma0Upper, mem_Gamma0Upper,
    jEquiv_apply, coe_jConjGammaH]
  show ((((ModularCurve.Period.jConjSL (γ : SL(2, ℤ)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℤ) :
      ZMod ℓ) = 0 ↔ ((((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℤ) : ZMod ℓ) = 0
  rw [ModularCurve.Period.jConjSL_coe, ModularCurve.Period.jConjMat_apply_zero_one, Int.cast_neg, neg_eq_zero]

theorem jConjSL_conjUpperMat (A : SL(2, ℤ)) (hb : (ℓ : ℤ) ∣ A 0 1)
    (hb' : (ℓ : ℤ) ∣ (ModularCurve.Period.jConjSL A : SL(2, ℤ)) 0 1) :
    ModularCurve.Period.jConjSL (conjUpperMat ℓ A hb) =
      conjUpperMat ℓ (ModularCurve.Period.jConjSL A) hb' := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  have h01 : (ModularCurve.Period.jConjSL A : SL(2, ℤ)) 0 1 = -(A 0 1) := by
    show (((ModularCurve.Period.jConjSL A : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 0 1 = -((A : Matrix (Fin 2) (Fin 2) ℤ) 0 1)
    rw [ModularCurve.Period.jConjSL_coe, ModularCurve.Period.jConjMat_apply_zero_one]
  have h00 : (ModularCurve.Period.jConjSL A : SL(2, ℤ)) 0 0 = A 0 0 := by
    show (((ModularCurve.Period.jConjSL A : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 0 0 = (A : Matrix (Fin 2) (Fin 2) ℤ) 0 0
    rw [ModularCurve.Period.jConjSL_coe, ModularCurve.Period.jConjMat_apply_zero_zero]
  have h10 : (ModularCurve.Period.jConjSL A : SL(2, ℤ)) 1 0 = -(A 1 0) := by
    show (((ModularCurve.Period.jConjSL A : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 = -((A : Matrix (Fin 2) (Fin 2) ℤ) 1 0)
    rw [ModularCurve.Period.jConjSL_coe, ModularCurve.Period.jConjMat_apply_one_zero]
  have h11 : (ModularCurve.Period.jConjSL A : SL(2, ℤ)) 1 1 = A 1 1 := by
    show (((ModularCurve.Period.jConjSL A : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 1 1 = (A : Matrix (Fin 2) (Fin 2) ℤ) 1 1
    rw [ModularCurve.Period.jConjSL_coe, ModularCurve.Period.jConjMat_apply_one_one]

  have lhs : ∀ i j, (ModularCurve.Period.jConjSL (conjUpperMat ℓ A hb) : SL(2, ℤ)) i j =
      ModularCurve.Period.jConjMat ((conjUpperMat ℓ A hb : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) i j :=
    fun i j => rfl
  rw [lhs]
  fin_cases i <;> fin_cases j
  · simp [conjUpperMat, ModularCurve.Period.jConjMat, h00]
  · simp only [conjUpperMat, ModularCurve.Period.jConjMat, Fin.zero_eta, Fin.mk_one, of_apply, cons_val',
      cons_val_one, cons_val_fin_one, cons_val_zero]
    show -(A 0 1 / ℓ) = (ModularCurve.Period.jConjSL A : SL(2, ℤ)) 0 1 / ℓ
    rw [h01, Int.neg_ediv_of_dvd hb]
  · simp only [conjUpperMat, ModularCurve.Period.jConjMat, Fin.mk_one, Fin.zero_eta, of_apply, cons_val',
      cons_val_zero, cons_val_fin_one, cons_val_one]
    show -(A 1 0 * ℓ) = (ModularCurve.Period.jConjSL A : SL(2, ℤ)) 1 0 * ℓ
    rw [h10, neg_mul]
  · simp [conjUpperMat, ModularCurve.Period.jConjMat, h11]

theorem jEquiv_conjL (γ : ↥(GammaHUpper M H ℓ)) :
    jEquiv M H (conjL M H ℓ γ) =
      conjL M H ℓ (resK (jEquiv M H) (GammaHUpper M H ℓ) (GammaHUpper M H ℓ)
        (jEquiv_mem_upper_iff M H ℓ) γ) := by
  apply Subtype.ext
  exact jConjSL_conjUpperMat ℓ _ (dvd_of_mem_GammaHUpper M H ℓ γ)
    (dvd_of_mem_GammaHUpper M H ℓ (resK (jEquiv M H) (GammaHUpper M H ℓ) (GammaHUpper M H ℓ)
      (jEquiv_mem_upper_iff M H ℓ) γ))

end JConj

section HeckeT

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ] (A : Type*) [AddCommGroup A]

open CohCarrier

theorem heckeT_apply_ofMul (φ : H1 M H A) (g : ↥(GammaH M H)) :
    heckeT M H ℓ A φ (Additive.ofMul g) =
      Multiplicative.toAdd (MonoidHom.transfer
        ((AddMonoidHom.toMultiplicativeRight φ).comp (conjL M H ℓ)) g) := rfl

theorem comp_conjL_charInvolution (R : Type*) [Semiring R] [Module R A] (φ : H1 M H A) :
    (AddMonoidHom.toMultiplicativeRight (charInvolution M H A R φ)).comp (conjL M H ℓ) =
      ((AddMonoidHom.toMultiplicativeRight φ).comp (conjL M H ℓ)).comp
        (resK (jEquiv M H) (GammaHUpper M H ℓ) (GammaHUpper M H ℓ) (jEquiv_mem_upper_iff M H ℓ)) := by
  refine MonoidHom.ext fun γ => ?_
  simp only [MonoidHom.comp_apply, AddMonoidHom.toMultiplicativeRight_apply_apply, charInvolution_apply,
    toMul_ofMul]
  congr 2
  rw [← jEquiv_apply, jEquiv_conjL]

theorem charInvolution_heckeT (R : Type*) [Semiring R] [Module R A] (φ : H1 M H A) :
    charInvolution M H A R (heckeT M H ℓ A φ) = heckeT M H ℓ A (charInvolution M H A R φ) := by
  refine AddMonoidHom.ext fun a => ?_
  obtain ⟨g, rfl⟩ : ∃ g : ↥(GammaH M H), Additive.ofMul g = a := ⟨Additive.toMul a, rfl⟩
  rw [charInvolution_apply, toMul_ofMul, heckeT_apply_ofMul, heckeT_apply_ofMul,
    comp_conjL_charInvolution, transfer_comp_resK, jEquiv_apply]

end HeckeT

section Diamond

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (𝒪 : Type) [CommRing 𝒪]

open CohCarrier

def jLift (σ : Gamma0 M) : Gamma0 M :=
  ⟨ModularCurve.Period.jConjSL (σ : SL(2, ℤ)), ModularCurve.Period.jConjSL_mem_Gamma0 σ.2⟩

theorem gamma0Units_jLift (σ : Gamma0 M) : gamma0Units M (jLift M σ) = gamma0Units M σ := by
  ext
  rfl

theorem charInvolution_diamondRaw (σ : Gamma0 M) (φ : H1 M H 𝒪) :
    charInvolution M H 𝒪 𝒪 (diamondRaw M H 𝒪 σ φ) = diamondRaw M H 𝒪 (jLift M σ) (charInvolution M H 𝒪 𝒪 φ) := by
  refine AddMonoidHom.ext fun a => ?_
  obtain ⟨g, rfl⟩ : ∃ g : ↥(GammaH M H), Additive.ofMul g = a := ⟨Additive.toMul a, rfl⟩
  show φ (Additive.ofMul (conjHom M H σ (jConjGammaH M H g))) =
    φ (Additive.ofMul (jConjGammaH M H (conjHom M H (jLift M σ) g)))
  congr 2
  apply Subtype.ext
  show (σ : SL(2, ℤ)) * ModularCurve.Period.jConjSL (g : SL(2, ℤ)) * (σ : SL(2, ℤ))⁻¹ =
    ModularCurve.Period.jConjSL (ModularCurve.Period.jConjSL (σ : SL(2, ℤ)) * (g : SL(2, ℤ)) *
      (ModularCurve.Period.jConjSL (σ : SL(2, ℤ)))⁻¹)
  rw [map_mul, map_mul, map_inv, ModularCurve.Period.jConjSL_jConjSL]

theorem charInvolution_diamondL (d : (ZMod M)ˣ) (φ : H1 M H 𝒪) :
    charInvolution M H 𝒪 𝒪 (diamondL M H 𝒪 d φ) = diamondL M H 𝒪 d (charInvolution M H 𝒪 𝒪 φ) := by
  obtain ⟨σ, hσ⟩ := gamma0Units_surjective M d
  rw [diamondL_eq_diamondRaw M H 𝒪 d σ hσ, diamondL_eq_diamondRaw M H 𝒪 d (jLift M σ)
    ((gamma0Units_jLift M σ).trans hσ), charInvolution_diamondRaw]

end Diamond

section OpFamily

open CohCarrier

theorem main (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪]
    (g : Gen M S) :
    charInvolution M H 𝒪 𝒪 ∘ₗ opFamily M H S 𝒪 g = opFamily M H S 𝒪 g ∘ₗ charInvolution M H 𝒪 𝒪 := by
  cases g with
  | T ℓ hℓ hℓS hℓM =>
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    refine LinearMap.ext fun φ => ?_
    show charInvolution M H 𝒪 𝒪 (heckeTL M H 𝒪 ℓ φ) = heckeTL M H 𝒪 ℓ (charInvolution M H 𝒪 𝒪 φ)
    rw [heckeTL_apply, heckeTL_apply]
    exact charInvolution_heckeT M H ℓ 𝒪 𝒪 φ
  | U q hq hqM =>
    haveI : NeZero q := ⟨hq.ne_zero⟩
    refine LinearMap.ext fun φ => ?_
    show charInvolution M H 𝒪 𝒪 (heckeTL M H 𝒪 q φ) = heckeTL M H 𝒪 q (charInvolution M H 𝒪 𝒪 φ)
    rw [heckeTL_apply, heckeTL_apply]
    exact charInvolution_heckeT M H q 𝒪 𝒪 φ
  | dia d =>
    refine LinearMap.ext fun φ => ?_
    exact charInvolution_diamondL M H 𝒪 d φ

end OpFamily

end CharInvHecke
p2m_reactivate "P2MW.S_CohCarrier_charInvolution_comp_opFamily.CharInvHecke"

theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ)
    (𝒪 : Type) [CommRing 𝒪] (g : CohCarrier.Gen M S) :
    CohCarrier.charInvolution M H 𝒪 𝒪 ∘ₗ CohCarrier.opFamily M H S 𝒪 g =
      CohCarrier.opFamily M H S 𝒪 g ∘ₗ CohCarrier.charInvolution M H 𝒪 𝒪 :=
  CharInvHecke.main M H S 𝒪 g

end S_CohCarrier_charInvolution_comp_opFamily
end P2MW
export P2MW.S_CohCarrier_charInvolution_comp_opFamily (solution)
