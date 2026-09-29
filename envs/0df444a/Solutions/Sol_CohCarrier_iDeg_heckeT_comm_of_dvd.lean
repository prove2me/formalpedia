-- Prove2me | solution 1 for CohCarrier.iDeg_heckeT_comm_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/d14d1921-0dfa-5abd-acaa-624737ea28c6

import Definitions.Def_CohCarrier_Level
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_iDeg_heckeT_comm_of_dvd

set_option autoImplicit false
open scoped MatrixGroups
open Subgroup Subgroup.leftTransversals CohCarrier CongruenceSubgroup

namespace SolAux
section NatInj
variable {G G' A : Type*} [Group G] [Group G'] [CommGroup A]

noncomputable def comapQuotientMap (f : G' →* G) (K : Subgroup G) :
    G' ⧸ (K.comap f) → G ⧸ K :=
  Quotient.map' f (fun a b hab => by
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    simpa using hab)

theorem comapQuotientMap_mk (f : G' →* G) (K : Subgroup G) (g' : G') :
    comapQuotientMap f K ↑g' = ↑(f g') := rfl

theorem comapQuotientMap_injective (f : G' →* G) (K : Subgroup G) :
    Function.Injective (comapQuotientMap f K) := by
  refine Quotient.ind₂' (fun a b hab => ?_)
  rw [comapQuotientMap_mk, comapQuotientMap_mk, QuotientGroup.eq] at hab
  rw [QuotientGroup.eq, Subgroup.mem_comap, map_mul, map_inv]
  exact hab

theorem index_comap_of_quotient_surjective (f : G' →* G) (K : Subgroup G) [K.FiniteIndex]
    (hsurj : Function.Surjective (comapQuotientMap f K)) :
    (K.comap f).index = K.index := by
  have e : G' ⧸ (K.comap f) ≃ G ⧸ K :=
    Equiv.ofBijective _ ⟨comapQuotientMap_injective f K, hsurj⟩
  simp only [Subgroup.index, Nat.card_congr e]

noncomputable def seedSection (f : G' →* G) (K : Subgroup G)
    (hsurj : Function.Surjective (comapQuotientMap f K)) :
    G ⧸ K → G :=
  fun q => f (Quotient.out
    ((Equiv.ofBijective _ ⟨comapQuotientMap_injective f K, hsurj⟩).symm q))

theorem seedSection_section (f : G' →* G) (K : Subgroup G)
    (hsurj : Function.Surjective (comapQuotientMap f K)) (q : G ⧸ K) :
    ((seedSection f K hsurj q : G) : G ⧸ K) = q := by
  set e := Equiv.ofBijective _ ⟨comapQuotientMap_injective f K, hsurj⟩
  calc ((seedSection f K hsurj q : G) : G ⧸ K)
      = comapQuotientMap f K ((Quotient.out (e.symm q) : G') : G' ⧸ K.comap f) := rfl
    _ = comapQuotientMap f K (e.symm q) := by
        exact congrArg (comapQuotientMap f K) (Quotient.out_eq' (e.symm q))
    _ = q := e.apply_symm_apply q

noncomputable def seedTransversal (f : G' →* G) (K : Subgroup G)
    (hsurj : Function.Surjective (comapQuotientMap f K)) :
    K.LeftTransversal :=
  ⟨Set.range (seedSection f K hsurj),
   Subgroup.isComplement_range_left (seedSection_section f K hsurj)⟩

theorem comapQuotientMap_smul (f : G' →* G) (K : Subgroup G) (g' : G') (q' : G' ⧸ K.comap f) :
    comapQuotientMap f K (g' • q') = (f g') • comapQuotientMap f K q' := by
  refine Quotient.inductionOn' q' (fun x => ?_)

  show comapQuotientMap f K ↑(g' * x) = (f g') • (↑(f x) : G ⧸ K)
  rw [comapQuotientMap_mk, map_mul]
  rfl

theorem seedTransversal_lqe (f : G' →* G) (K : Subgroup G) [K.FiniteIndex]
    (hsurj : Function.Surjective (comapQuotientMap f K)) (q : G ⧸ K) :
    ((seedTransversal f K hsurj).2.leftQuotientEquiv q : G) = seedSection f K hsurj q :=
  Subgroup.IsComplement.leftQuotientEquiv_apply (seedSection_section f K hsurj) q

theorem seedSection_e (f : G' →* G) (K : Subgroup G)
    (hsurj : Function.Surjective (comapQuotientMap f K)) (q' : G' ⧸ K.comap f) :
    seedSection f K hsurj
      (Equiv.ofBijective _ ⟨comapQuotientMap_injective f K, hsurj⟩ q') = f (Quotient.out q') := by
  unfold seedSection
  rw [Equiv.symm_apply_apply]

theorem seedSection_smul_e (f : G' →* G) (K : Subgroup G)
    (hsurj : Function.Surjective (comapQuotientMap f K)) (g' : G') (q' : G' ⧸ K.comap f) :
    seedSection f K hsurj
      ((f g')⁻¹ • Equiv.ofBijective _ ⟨comapQuotientMap_injective f K, hsurj⟩ q')
      = f (Quotient.out ((g')⁻¹ • q')) := by
  have h1 : (f g')⁻¹ • (Equiv.ofBijective _ ⟨comapQuotientMap_injective f K, hsurj⟩ q')
      = Equiv.ofBijective _ ⟨comapQuotientMap_injective f K, hsurj⟩ ((g')⁻¹ • q') := by
    show (f g')⁻¹ • comapQuotientMap f K q' = comapQuotientMap f K ((g')⁻¹ • q')
    rw [← map_inv, ← comapQuotientMap_smul]
  rw [h1, seedSection_e]

open Subgroup Subgroup.leftTransversals MulAction in

theorem transfer_nat_inj (f : G' →* G) {K : Subgroup G} [K.FiniteIndex] (ψ : ↥K →* A)
    (hsurj : Function.Surjective (comapQuotientMap f K))
    [(K.comap f).FiniteIndex] (g' : G') :
    ψ.transfer (f g') = (ψ.comp (f.subgroupComap K)).transfer g' := by
  set e := Equiv.ofBijective _ ⟨comapQuotientMap_injective f K, hsurj⟩ with he
  letI : Fintype (G ⧸ K) := K.fintypeQuotientOfFiniteIndex
  letI : Fintype (G' ⧸ K.comap f) := (K.comap f).fintypeQuotientOfFiniteIndex
  rw [ψ.transfer_def (seedTransversal f K hsurj),
    (ψ.comp (f.subgroupComap K)).transfer_def default]
  dsimp only [diff]
  refine Eq.symm (Fintype.prod_equiv (M := A) e _ _ (fun q' => Eq.symm ?_))

  rw [MonoidHom.comp_apply]
  congr 1
  apply Subtype.ext

  show ((seedTransversal f K hsurj).2.leftQuotientEquiv (e q') : G)⁻¹
      * ↑((f g' • seedTransversal f K hsurj).2.leftQuotientEquiv (e q'))
    = f ((((default : (K.comap f).LeftTransversal)).2.leftQuotientEquiv q' : G')⁻¹
      * ((g' • (default : (K.comap f).LeftTransversal)).2.leftQuotientEquiv q' : G'))
  rw [seedTransversal_lqe, smul_apply_eq_smul_apply_inv_smul, seedTransversal_lqe,
    he, seedSection_e, seedSection_smul_e,
    smul_apply_eq_smul_apply_inv_smul,
    show (((default : (K.comap f).LeftTransversal)).2.leftQuotientEquiv q' : G')
      = Quotient.out q' from Subgroup.IsComplement.leftQuotientEquiv_apply Quotient.out_eq' q',
    show (((default : (K.comap f).LeftTransversal)).2.leftQuotientEquiv ((g')⁻¹ • q') : G')
      = Quotient.out ((g')⁻¹ • q') from
        Subgroup.IsComplement.leftQuotientEquiv_apply Quotient.out_eq' _]
  simp only [smul_eq_mul, map_mul, map_inv]

theorem comapQuotientMap_surjective_of_index_eq (f : G' →* G) (K : Subgroup G)
    [K.FiniteIndex] [(K.comap f).FiniteIndex]
    (hidx : (K.comap f).index = K.index) :
    Function.Surjective (comapQuotientMap f K) := by
  have hfin : Finite (G ⧸ K) := Nat.finite_of_card_ne_zero Subgroup.FiniteIndex.index_ne_zero
  have hfin' : Finite (G' ⧸ K.comap f) :=
    Nat.finite_of_card_ne_zero Subgroup.FiniteIndex.index_ne_zero
  letI := Fintype.ofFinite (G ⧸ K)
  letI := Fintype.ofFinite (G' ⧸ K.comap f)
  exact ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨comapQuotientMap_injective f K, by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]; exact hidx⟩).surjective

end NatInj

theorem transfer_subgroupCongr {G C : Type*} [Group G] [CommGroup C] {K₁ K₂ : Subgroup G}
    (hK : K₁ = K₂) [K₁.FiniteIndex] [K₂.FiniteIndex] (ψ : ↥K₂ →* C) :
    MonoidHom.transfer (ψ.comp (MulEquiv.subgroupCongr hK).toMonoidHom) = ψ.transfer := by
  subst hK
  have hψ : ψ.comp (MulEquiv.subgroupCongr rfl).toMonoidHom = ψ :=
    MonoidHom.ext fun k => congrArg ψ (Subtype.ext rfl)
  rw [hψ]

section DeiT
variable {M M' : ℕ} {H : Subgroup (ZMod M)ˣ} {H' : Subgroup (ZMod M')ˣ} {d ℓ : ℕ}

@[scoped simp] theorem conjLowerMat_01 (X : SL(2, ℤ)) (hX : (d : ℤ) ∣ X 1 0) :
    (conjLowerMat d X hX : SL(2, ℤ)) 0 1 = X 0 1 * d := by
  simp [conjLowerMat]

theorem comap_GammaHUpper_iotaDeg [NeZero d] (h : LevelLE M M' H H' d) (hℓd : Nat.Coprime ℓ d) :
    (GammaHUpper M H ℓ).comap (iotaDeg M M' H H' d h) = GammaHUpper M' H' ℓ := by
  ext γ
  simp only [Subgroup.mem_comap, GammaHUpper, Subgroup.mem_subgroupOf, mem_Gamma0Upper]
  show ((conjLowerMat d (γ : SL(2, ℤ)) (h.dvd_entry γ) : SL(2, ℤ)) 0 1 : ZMod ℓ) = 0
    ↔ ((γ : SL(2, ℤ)) 0 1 : ZMod ℓ) = 0
  rw [conjLowerMat_01, ZMod.intCast_zmod_eq_zero_iff_dvd, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hcop : IsCoprime (ℓ : ℤ) (d : ℤ) :=
    Int.isCoprime_iff_gcd_eq_one.mpr (by exact_mod_cast hℓd)
  exact ⟨fun hdvd => hcop.dvd_of_dvd_mul_right hdvd,
    fun hdvd => Dvd.dvd.mul_right hdvd d⟩

theorem conjUpperMat_conjLowerMat_comm (X : SL(2, ℤ))
    (hℓ : (ℓ : ℤ) ∣ X 0 1) (hd : (d : ℤ) ∣ X 1 0)
    (hℓ' : (ℓ : ℤ) ∣ (conjLowerMat d X hd : SL(2, ℤ)) 0 1)
    (hd' : (d : ℤ) ∣ (conjUpperMat ℓ X hℓ : SL(2, ℤ)) 1 0) :
    conjUpperMat ℓ (conjLowerMat d X hd) hℓ'
      = conjLowerMat d (conjUpperMat ℓ X hℓ) hd' := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [conjUpperMat, conjLowerMat, Int.mul_ediv_assoc _ hℓ, mul_comm]
  exact (Int.mul_ediv_assoc (ℓ : ℤ) hd).symm

end DeiT
end SolAux
p2m_reactivate "P2MW.S_CohCarrier_iDeg_heckeT_comm_of_dvd.SolAux"

namespace IharaMintIdx

theorem mul_inv_apply_01 (x y : SL(2, ℤ)) : (x * y⁻¹) 0 1 = -(x 0 0 * y 0 1) + x 0 1 * y 0 0 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two]
  simp only [Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

def uMat (t : ℤ) : SL(2, ℤ) :=
  ⟨!![1, t; 0, 1], by rw [Matrix.det_fin_two_of]; ring⟩

@[scoped simp] theorem uMat_00 (t : ℤ) : (uMat t) 0 0 = 1 := rfl
@[scoped simp] theorem uMat_01 (t : ℤ) : (uMat t) 0 1 = t := rfl

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ)

theorem uMat_mem (t : ℤ) : uMat t ∈ CohCarrier.GammaH M H := by
  have h0 : uMat t ∈ Gamma0 M := by
    rw [Gamma0_mem]
    show ((0 : ℤ) : ZMod M) = 0
    exact Int.cast_zero
  refine CohCarrier.mem_GammaH_iff.mpr ⟨h0, ?_⟩
  have e : CohCarrier.gamma0Units M ⟨uMat t, h0⟩ = 1 := by
    apply Units.ext
    rw [CohCarrier.val_gamma0Units, Units.val_one]
    show ((1 : ℤ) : ZMod M) = 1
    exact Int.cast_one
  rw [e]
  exact H.one_mem

def uElt (t : ℤ) : ↥(CohCarrier.GammaH M H) := ⟨uMat t, uMat_mem M H t⟩

@[scoped simp] theorem uElt_coe (t : ℤ) : ((uElt M H t : ↥(CohCarrier.GammaH M H)) : SL(2, ℤ)) = uMat t := rfl

theorem mk_eq_mk_iff (x y : ↥(CohCarrier.GammaH M H)) :
    (Quotient.mk'' x : Quotient (QuotientGroup.rightRel (CohCarrier.GammaHUpper M H ℓ))) = Quotient.mk'' y ↔
      ((((y : SL(2, ℤ)) * (x : SL(2, ℤ))⁻¹) 0 1 : ℤ) : ZMod ℓ) = 0 := by
  rw [Quotient.eq'', QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf, CohCarrier.mem_Gamma0Upper, Subgroup.coe_mul,
    Subgroup.coe_inv]

theorem natCard_rightQuot [NeZero ℓ] (hℓM : ℓ ∣ M) :
    Nat.card (Quotient (QuotientGroup.rightRel (CohCarrier.GammaHUpper M H ℓ))) = ℓ := by
  have hUU : ∀ j j' : ZMod ℓ,
      (Quotient.mk'' (uElt M H (j.val : ℤ)) : Quotient (QuotientGroup.rightRel (CohCarrier.GammaHUpper M H ℓ))) =
        Quotient.mk'' (uElt M H (j'.val : ℤ)) → j = j' := by
    intro j j' h
    rw [mk_eq_mk_iff, mul_inv_apply_01] at h
    simp only [uElt_coe, uMat_00, uMat_01] at h
    push_cast at h
    simp only [ZMod.natCast_zmod_val] at h
    linear_combination -h
  let ψ : ZMod ℓ → Quotient (QuotientGroup.rightRel (CohCarrier.GammaHUpper M H ℓ)) :=
    fun j => Quotient.mk'' (uElt M H (j.val : ℤ))
  have hinj : Function.Injective ψ := fun j j' h => hUU j j' h
  have hsurj : Function.Surjective ψ := by
    intro q
    induction q using Quotient.inductionOn' with
    | h g =>
      have hdet := Matrix.SpecialLinearGroup.det_coe (g : SL(2, ℤ))
      rw [Matrix.det_fin_two] at hdet
      have hdet' := congrArg (Int.cast : ℤ → ZMod ℓ) hdet
      push_cast at hdet'
      have hg0 : ((g : SL(2, ℤ)) : SL(2, ℤ)) ∈ Gamma0 M := (CohCarrier.mem_GammaH_iff.mp g.2).1
      have hc : ((((g : SL(2, ℤ)) 1 0 : ℤ)) : ZMod ℓ) = 0 := by
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
        rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hg0
        exact dvd_trans (Int.natCast_dvd_natCast.mpr hℓM) hg0
      refine ⟨(((g : SL(2, ℤ)) 1 1 : ℤ) : ZMod ℓ) * (((g : SL(2, ℤ)) 0 1 : ℤ) : ZMod ℓ), ?_⟩
      show (Quotient.mk'' (uElt M H (((((g : SL(2, ℤ)) 1 1 : ℤ) : ZMod ℓ) *
          (((g : SL(2, ℤ)) 0 1 : ℤ) : ZMod ℓ)).val : ℤ)) :
          Quotient (QuotientGroup.rightRel (CohCarrier.GammaHUpper M H ℓ))) = Quotient.mk'' g
      rw [mk_eq_mk_iff, mul_inv_apply_01]
      simp only [uElt_coe, uMat_00, uMat_01]
      push_cast
      rw [ZMod.natCast_zmod_val]
      linear_combination (-((((g : SL(2, ℤ)) 0 1 : ℤ)) : ZMod ℓ)) * hdet'
        + (-(((((g : SL(2, ℤ)) 0 1 : ℤ)) : ZMod ℓ) * ((((g : SL(2, ℤ)) 0 1 : ℤ)) : ZMod ℓ))) * hc
  rw [← Nat.card_congr (Equiv.ofBijective ψ ⟨hinj, hsurj⟩), Nat.card_eq_fintype_card, ZMod.card]

end IharaMintIdx
p2m_reactivate "P2MW.S_CohCarrier_iDeg_heckeT_comm_of_dvd.SolAux P2MW.S_CohCarrier_iDeg_heckeT_comm_of_dvd.IharaMintIdx"

namespace SolAux
theorem index_GammaHUpper_of_dvd_impl (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ]
    (hℓM : ℓ ∣ M) : (CohCarrier.GammaHUpper M H ℓ).index = ℓ := by
  rw [Subgroup.index,
    ← Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel (GammaHUpper M H ℓ))]
  exact IharaMintIdx.natCard_rightQuot M H ℓ hℓM
end SolAux
p2m_reactivate "P2MW.S_CohCarrier_iDeg_heckeT_comm_of_dvd.SolAux P2MW.S_CohCarrier_iDeg_heckeT_comm_of_dvd.IharaMintIdx"

open SolAux

theorem solution {M M' : ℕ} {H : Subgroup (ZMod M)ˣ} {H' : Subgroup (ZMod M')ˣ} {d ℓ : ℕ}
    {A : Type} [AddCommGroup A] [NeZero d] [NeZero ℓ] (h : LevelLE M M' H H' d)
    (hℓd : Nat.Coprime ℓ d) (hℓM : ℓ ∣ M) (φ : H1 M H A) :
    iDeg' M M' H H' d A h (heckeT M H ℓ A φ)
      = heckeT M' H' ℓ A (iDeg' M M' H H' d A h φ) := by
  set f := iotaDeg M M' H H' d h with hf
  set K := GammaHUpper M H ℓ with hK
  have hA : K.comap f = GammaHUpper M' H' ℓ := comap_GammaHUpper_iotaDeg h hℓd
  haveI : (K.comap f).FiniteIndex := hA ▸ inferInstance
  have hsurj : Function.Surjective (comapQuotientMap f K) := by
    refine comapQuotientMap_surjective_of_index_eq f K ?_
    rw [hA]
    exact (index_GammaHUpper_of_dvd_impl M' H' ℓ (dvd_trans hℓM h.dvd)).trans
      (index_GammaHUpper_of_dvd_impl M H ℓ hℓM).symm
  ext γ'
  show MonoidHom.transfer
      ((AddMonoidHom.toMultiplicativeRight φ).comp (conjL M H ℓ)) (f (Additive.toMul γ'))
    = MonoidHom.transfer
      ((AddMonoidHom.toMultiplicativeRight (iDeg' M M' H H' d A h φ)).comp (conjL M' H' ℓ))
      (Additive.toMul γ')
  rw [transfer_nat_inj f _ hsurj]
  rw [← transfer_subgroupCongr hA
    ((AddMonoidHom.toMultiplicativeRight (iDeg' M M' H H' d A h φ)).comp (conjL M' H' ℓ))]
  have hchar : ((AddMonoidHom.toMultiplicativeRight φ).comp (conjL M H ℓ)).comp
        (f.subgroupComap K)
      = ((AddMonoidHom.toMultiplicativeRight (iDeg' M M' H H' d A h φ)).comp
          (conjL M' H' ℓ)).comp (MulEquiv.subgroupCongr hA).toMonoidHom := by
    refine MonoidHom.ext fun k => ?_
    have hmat : (conjL M H ℓ) ((f.subgroupComap K) k)
        = f ((conjL M' H' ℓ) ((MulEquiv.subgroupCongr hA) k)) := by
      have hk' : (k : ↥(GammaH M' H')) ∈ GammaHUpper M' H' ℓ := hA ▸ k.2
      have hℓX : (ℓ : ℤ) ∣ ((k : ↥(GammaH M' H')) : SL(2, ℤ)) 0 1 :=
        dvd_of_mem_GammaHUpper M' H' ℓ ⟨(k : ↥(GammaH M' H')), hk'⟩
      have hdX : (d : ℤ) ∣ ((k : ↥(GammaH M' H')) : SL(2, ℤ)) 1 0 :=
        h.dvd_entry (k : ↥(GammaH M' H'))
      have hℓ' : (ℓ : ℤ) ∣
          (conjLowerMat d ((k : ↥(GammaH M' H')) : SL(2, ℤ)) hdX : SL(2, ℤ)) 0 1 := by
        rw [conjLowerMat_01]; exact hℓX.mul_right _
      have hd' : (d : ℤ) ∣
          (conjUpperMat ℓ ((k : ↥(GammaH M' H')) : SL(2, ℤ)) hℓX : SL(2, ℤ)) 1 0 := by
        rw [conjUpperMat_apply_10]; exact hdX.mul_right _
      exact Subtype.ext (conjUpperMat_conjLowerMat_comm _ hℓX hdX hℓ' hd')
    show (AddMonoidHom.toMultiplicativeRight φ) ((conjL M H ℓ) ((f.subgroupComap K) k))
        = (AddMonoidHom.toMultiplicativeRight (iDeg' M M' H H' d A h φ))
            ((conjL M' H' ℓ) ((MulEquiv.subgroupCongr hA) k))
    rw [hmat]
    rfl
  rw [hchar]

#print axioms solution

end S_CohCarrier_iDeg_heckeT_comm_of_dvd
end P2MW
export P2MW.S_CohCarrier_iDeg_heckeT_comm_of_dvd (solution)
