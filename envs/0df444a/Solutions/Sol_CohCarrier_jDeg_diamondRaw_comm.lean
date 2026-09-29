-- Prove2me | solution 1 for CohCarrier.jDeg_diamondRaw_comm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/67050c62-0134-55f9-a45d-3b6271b374f2

import Definitions.Def_CohCarrier_Level
import Mathlib.GroupTheory.QuotientGroup.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_jDeg_diamondRaw_comm

set_option autoImplicit false
open scoped MatrixGroups
open Subgroup Subgroup.leftTransversals CohCarrier CongruenceSubgroup

namespace IharaMintJD

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

section Anti
variable (M M' : ℕ)

theorem Gamma0_anti (hMM' : M ∣ M') : Gamma0 M' ≤ Gamma0 M := by
  intro A hA
  rw [Gamma0_mem] at hA ⊢
  have : ((A 1 0 : ℤ) : ZMod M) = ZMod.castHom hMM' (ZMod M) ((A 1 0 : ℤ) : ZMod M') :=
    (map_intCast (ZMod.castHom hMM' (ZMod M)) _).symm
  rw [this, hA, map_zero]

end Anti

variable (M M' : ℕ) (H : Subgroup (ZMod M)ˣ) (H' : Subgroup (ZMod M')ˣ) (d : ℕ)
variable (A : Type*) [AddCommGroup A]
variable (ℓ : ℕ) [NeZero ℓ] [NeZero d] [NeZero M'] (h : LevelLE M M' H H' d)

section iDeg

omit [NeZero ℓ] [NeZero d] [NeZero M'] in
include h in

theorem dvd_lowerLeft_of_Gamma0_M' (σ' : Gamma0 M') :
    (d : ℤ) ∣ (σ' : SL(2, ℤ)) 1 0 := by
  have hM' : (M' : ℤ) ∣ (σ' : SL(2, ℤ)) 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp σ'.2)
  obtain ⟨e, he⟩ := h.exists_eq
  refine dvd_trans ?_ hM'
  rw [he]; push_cast; exact ⟨(M : ℤ) * e, by ring⟩

def compensator (σ' : Gamma0 M') : SL(2, ℤ) :=
  conjLowerMat d (σ' : SL(2, ℤ)) (dvd_lowerLeft_of_Gamma0_M' M M' H H' d h σ')
    * (σ' : SL(2, ℤ))⁻¹

omit [NeZero ℓ] [NeZero M'] in
include h in

theorem M_dvd_lowerLeft_div_d (σ' : Gamma0 M') :
    (M : ℤ) ∣ (σ' : SL(2, ℤ)) 1 0 / (d : ℤ) := by
  have hM' : (M' : ℤ) ∣ (σ' : SL(2, ℤ)) 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp σ'.2)
  obtain ⟨k, hk⟩ := hM'
  obtain ⟨e, he⟩ := h.exists_eq
  refine ⟨e * k, ?_⟩
  rw [hk, he]
  push_cast
  rw [show (M : ℤ) * (d * e) * k = d * (M * (e * k)) from by ring,
    Int.mul_ediv_cancel_left _ (by exact_mod_cast NeZero.ne d)]

omit [NeZero ℓ] [NeZero d] [NeZero M'] in

theorem compensator_apply_10 (σ' : Gamma0 M') :
    (compensator M M' H H' d h σ' : SL(2, ℤ)) 1 0
      = (σ' : SL(2, ℤ)) 1 1 * ((σ' : SL(2, ℤ)) 1 0 / (d : ℤ) - (σ' : SL(2, ℤ)) 1 0) := by
  unfold compensator
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl (σ' : SL(2, ℤ))]
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
    conjLowerMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  ring

omit [NeZero ℓ] [NeZero d] [NeZero M'] in

theorem compensator_apply_11 (σ' : Gamma0 M') :
    (compensator M M' H H' d h σ' : SL(2, ℤ)) 1 1
      = 1 + (σ' : SL(2, ℤ)) 0 1 * ((σ' : SL(2, ℤ)) 1 0 - (σ' : SL(2, ℤ)) 1 0 / (d : ℤ)) := by
  unfold compensator
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl (σ' : SL(2, ℤ))]
  have hdet : (σ' : SL(2, ℤ)) 0 0 * (σ' : SL(2, ℤ)) 1 1
      - (σ' : SL(2, ℤ)) 0 1 * (σ' : SL(2, ℤ)) 1 0 = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe (σ' : SL(2, ℤ))
    rw [Matrix.det_fin_two] at this
    linarith
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
    conjLowerMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  linarith [hdet]

omit [NeZero ℓ] [NeZero M'] in

theorem compensator_mem_GammaH (σ' : Gamma0 M') :
    compensator M M' H H' d h σ' ∈ GammaH M H := by
  have hMd : (M : ℤ) ∣ (σ' : SL(2, ℤ)) 1 0 / (d : ℤ) := M_dvd_lowerLeft_div_d M M' H H' d h σ'
  have hM : (M : ℤ) ∣ (σ' : SL(2, ℤ)) 1 0 :=
    dvd_trans (by exact_mod_cast h.dvd)
      ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp σ'.2))
  have h10 : (((compensator M M' H H' d h σ' : SL(2, ℤ)) 1 0 : ℤ) : ZMod M) = 0 := by
    rw [compensator_apply_10, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact Dvd.dvd.mul_left (dvd_sub hMd hM) _
  have h11 : (((compensator M M' H H' d h σ' : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) = 1 := by
    rw [compensator_apply_11]
    have e1 : (((σ' : SL(2, ℤ)) 1 0 : ℤ) : ZMod M) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hM
    have e2 : (((σ' : SL(2, ℤ)) 1 0 / (d : ℤ) : ℤ) : ZMod M) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hMd
    push_cast
    rw [e1, e2]
    ring
  rw [mem_GammaH_iff]
  refine ⟨Gamma0_mem.mpr h10, ?_⟩

  have hu : gamma0Units M ⟨_, Gamma0_mem.mpr h10⟩ = 1 := by
    ext; exact h11
  rw [hu]
  exact H.one_mem

omit [NeZero ℓ] [NeZero d] [NeZero M'] in

theorem conjLowerMat_one' :
    conjLowerMat d (1 : SL(2, ℤ)) (dvd_zero _) = 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [conjLowerMat]

omit [NeZero ℓ] [NeZero d] [NeZero M'] in

theorem dvd_inv_lowerLeft (X : SL(2, ℤ)) (hX : (d : ℤ) ∣ X 1 0) :
    (d : ℤ) ∣ (X⁻¹ : SL(2, ℤ)) 1 0 := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  simpa using dvd_neg.mpr hX

omit [NeZero ℓ] [NeZero d] [NeZero M'] in

theorem conjLowerMat_inv' (X : SL(2, ℤ)) (hX : (d : ℤ) ∣ X 1 0) :
    conjLowerMat d X⁻¹ (dvd_inv_lowerLeft d X hX)
      = (conjLowerMat d X hX)⁻¹ := by

  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl (conjLowerMat d X hX)]
  fin_cases i <;> fin_cases j <;>
    simp [conjLowerMat, Matrix.SpecialLinearGroup.SL2_inv_expl X, Int.neg_ediv_of_dvd hX]

omit [NeZero ℓ] [NeZero M'] in

theorem conjHom_iotaDeg_eq (σ' : Gamma0 M') (γ : ↥(GammaH M' H')) :
    iotaDeg M M' H H' d h (conjHom M' H' σ' γ)
      = ⟨compensator M M' H H' d h σ', compensator_mem_GammaH M M' H H' d h σ'⟩
        * conjHom M H ⟨σ'.1, Gamma0_anti M M' h.dvd σ'.2⟩ (iotaDeg M M' H H' d h γ)
        * (⟨compensator M M' H H' d h σ', compensator_mem_GammaH M M' H H' d h σ'⟩ :
            ↥(GammaH M H))⁻¹ := by
  apply Subtype.ext

  have hdσ : (d : ℤ) ∣ (σ' : SL(2, ℤ)) 1 0 := dvd_lowerLeft_of_Gamma0_M' M M' H H' d h σ'
  have hdγ : (d : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 := h.dvd_entry γ
  have hdσγ : (d : ℤ) ∣ ((σ' : SL(2, ℤ)) * (γ : SL(2, ℤ))) 1 0 := by
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    exact dvd_add (Dvd.dvd.mul_right hdσ _) (Dvd.dvd.mul_left hdγ _)

  have eLHS : ((iotaDeg M M' H H' d h (conjHom M' H' σ' γ)) : SL(2, ℤ))
      = conjLowerMat d (σ' : SL(2, ℤ)) hdσ
        * conjLowerMat d (γ : SL(2, ℤ)) hdγ
        * (conjLowerMat d (σ' : SL(2, ℤ)) hdσ)⁻¹ := by
    have hdprod : (d : ℤ) ∣ ((σ' : SL(2, ℤ)) * (γ : SL(2, ℤ)) * (σ' : SL(2, ℤ))⁻¹) 1 0 :=
      h.dvd_entry (conjHom M' H' σ' γ)
    calc ((iotaDeg M M' H H' d h (conjHom M' H' σ' γ)) : SL(2, ℤ))
        = conjLowerMat d ((σ' : SL(2, ℤ)) * (γ : SL(2, ℤ)) * (σ' : SL(2, ℤ))⁻¹) hdprod := rfl
      _ = _ := by
        rw [conjLowerMat_mul d ((σ' : SL(2, ℤ)) * (γ : SL(2, ℤ))) ((σ' : SL(2, ℤ))⁻¹) hdσγ
            (dvd_inv_lowerLeft d _ hdσ) hdprod,
          conjLowerMat_mul d (σ' : SL(2, ℤ)) (γ : SL(2, ℤ)) hdσ hdγ hdσγ,
          conjLowerMat_inv' d (σ' : SL(2, ℤ)) hdσ]

  simp only [Subgroup.coe_mul, Subgroup.coe_inv, eLHS]
  show _ = compensator M M' H H' d h σ'
    * ((σ' : SL(2, ℤ)) * conjLowerMat d (γ : SL(2, ℤ)) hdγ * (σ' : SL(2, ℤ))⁻¹)
    * (compensator M M' H H' d h σ')⁻¹
  unfold compensator
  group

end iDeg
end IharaMintJD

namespace IharaMintJD
variable {M M' : ℕ} {H : Subgroup (ZMod M)ˣ} {H' : Subgroup (ZMod M')ˣ} {d ℓ : ℕ}
  {A : Type} [AddCommGroup A]

section DEjD

theorem conjHom_apply_coe (σ : Gamma0 M) (x : ↥(GammaH M H)) :
    ((conjHom M H σ x : ↥(GammaH M H)) : SL(2, ℤ))
      = (σ : SL(2, ℤ)) * (x : SL(2, ℤ)) * (σ : SL(2, ℤ))⁻¹ := rfl

theorem conjHom_cancel₁ (σ : Gamma0 M) (x : ↥(GammaH M H)) :
    conjHom M H σ (conjHom M H σ⁻¹ x) = x := by
  apply Subtype.ext
  rw [conjHom_apply_coe, conjHom_apply_coe]
  push_cast
  group

theorem conjHom_cancel₂ (σ : Gamma0 M) (x : ↥(GammaH M H)) :
    conjHom M H σ⁻¹ (conjHom M H σ x) = x := by
  apply Subtype.ext
  rw [conjHom_apply_coe, conjHom_apply_coe]
  push_cast
  group

theorem comapQuotientMap_conjHom_surjective (σ : Gamma0 M) (K : Subgroup ↥(GammaH M H)) :
    Function.Surjective (comapQuotientMap (conjHom M H σ) K) := by
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨((conjHom M H σ⁻¹ g : ↥(GammaH M H)) : _ ⧸ _), ?_⟩
  rw [comapQuotientMap_mk]
  congr 1
  exact conjHom_cancel₁ σ g

theorem comp_conjHom_of_mem {C : Type*} [CommGroup C] (f : ↥(GammaH M H) →* C)
    (c : ↥(GammaH M H)) :
    f.comp (conjHom M H ⟨(c : SL(2, ℤ)), GammaH_le_Gamma0 H c.2⟩) = f := by
  ext g
  have hc : conjHom M H ⟨(c : SL(2, ℤ)), GammaH_le_Gamma0 H c.2⟩ g = c * g * c⁻¹ :=
    Subtype.ext rfl
  show f (conjHom M H ⟨(c : SL(2, ℤ)), GammaH_le_Gamma0 H c.2⟩ g) = f g
  rw [hc, f.map_mul, f.map_mul, f.map_inv, mul_comm (f c) (f g), mul_assoc,
    mul_inv_cancel, mul_one]

def innerComp [NeZero d] [NeZero M'] (σ' : Gamma0 M') (h : LevelLE M M' H H' d) : ↥(GammaH M H) :=
  conjHom M H (⟨σ'.1, Gamma0_anti M M' h.dvd σ'.2⟩ : Gamma0 M)⁻¹
    ⟨compensator M M' H H' d h σ', compensator_mem_GammaH M M' H H' d h σ'⟩

theorem key_conj_iotaDeg [NeZero d] [NeZero M'] (σ' : Gamma0 M') (h : LevelLE M M' H H' d)
    (δ : ↥(GammaH M' H')) :
    conjHom M H (⟨σ'.1, Gamma0_anti M M' h.dvd σ'.2⟩ : Gamma0 M)⁻¹
        (iotaDeg M M' H H' d h δ)
      = innerComp σ' h * iotaDeg M M' H H' d h (conjHom M' H' σ'⁻¹ δ)
          * (innerComp σ' h)⁻¹ := by
  have hsq := conjHom_iotaDeg_eq M M' H H' d h σ' (conjHom M' H' σ'⁻¹ δ)
  rw [conjHom_cancel₁] at hsq
  have h2 := congrArg (conjHom M H (⟨σ'.1, Gamma0_anti M M' h.dvd σ'.2⟩ : Gamma0 M)⁻¹) hsq
  rw [map_mul, map_mul, map_inv, conjHom_cancel₂] at h2
  exact h2

theorem comap_conjHom_range [NeZero d] [NeZero M'] (σ' : Gamma0 M') (h : LevelLE M M' H H' d) :
    (iotaDeg M M' H H' d h).range.comap
        (conjHom M H (⟨σ'.1, Gamma0_anti M M' h.dvd σ'.2⟩ : Gamma0 M))
      = (iotaDeg M M' H H' d h).range.comap
        (conjHom M H ⟨(((innerComp σ' h)⁻¹ : ↥(GammaH M H)) : SL(2, ℤ)),
          GammaH_le_Gamma0 H ((innerComp σ' h)⁻¹).2⟩) := by
  have hinner : ∀ x : ↥(GammaH M H),
      conjHom M H ⟨(((innerComp σ' h)⁻¹ : ↥(GammaH M H)) : SL(2, ℤ)),
        GammaH_le_Gamma0 H ((innerComp σ' h)⁻¹).2⟩ x
        = (innerComp σ' h)⁻¹ * x * innerComp σ' h := by
    intro x
    apply Subtype.ext
    rw [conjHom_apply_coe]
    push_cast
    group
  ext x
  simp only [mem_comap, MonoidHom.mem_range]
  constructor
  · rintro ⟨δ, hδ⟩
    refine ⟨conjHom M' H' σ'⁻¹ δ, ?_⟩
    have hx : x = innerComp σ' h * iotaDeg M M' H H' d h (conjHom M' H' σ'⁻¹ δ)
        * (innerComp σ' h)⁻¹ := by
      rw [← key_conj_iotaDeg σ' h δ, hδ, conjHom_cancel₂]
    rw [hinner, hx]
    group
  · rintro ⟨w, hw⟩
    refine ⟨conjHom M' H' σ' w, ?_⟩
    rw [hinner] at hw
    have hx : x = innerComp σ' h * iotaDeg M M' H H' d h w * (innerComp σ' h)⁻¹ := by
      rw [hw]
      group
    have hkey := key_conj_iotaDeg σ' h (conjHom M' H' σ' w)
    rw [conjHom_cancel₂] at hkey
    rw [hx, ← hkey, conjHom_cancel₁]

set_option maxHeartbeats 1600000 in

theorem jDeg_diamond_intertwine_impl [NeZero d] [NeZero M'] (σ' : Gamma0 M')
    (h : LevelLE M M' H H' d) (φ : H1 M' H' A) :
    diamondRaw M H A ⟨σ'.1, Gamma0_anti M M' h.dvd σ'.2⟩ (jDeg M M' H H' d A h φ)
      = jDeg M M' H H' d A h (diamondRaw M' H' A σ' φ) := by
  classical
  have hsub := comap_conjHom_range σ' h
  have hidxσ : ((iotaDeg M M' H H' d h).range.comap
      (conjHom M H (⟨σ'.1, Gamma0_anti M M' h.dvd σ'.2⟩ : Gamma0 M))).index
      = (iotaDeg M M' H H' d h).range.index :=
    Nat.card_eq_of_bijective _
      ⟨comapQuotientMap_injective _ _, comapQuotientMap_conjHom_surjective _ _⟩
  haveI hfiσ : ((iotaDeg M M' H H' d h).range.comap
      (conjHom M H (⟨σ'.1, Gamma0_anti M M' h.dvd σ'.2⟩ : Gamma0 M))).FiniteIndex :=
    ⟨by rw [hidxσ]; exact Subgroup.FiniteIndex.index_ne_zero⟩
  haveI hfic : ((iotaDeg M M' H H' d h).range.comap
      (conjHom M H ⟨(((innerComp σ' h)⁻¹ : ↥(GammaH M H)) : SL(2, ℤ)),
        GammaH_le_Gamma0 H ((innerComp σ' h)⁻¹).2⟩)).FiniteIndex := by
    rw [← hsub]; exact hfiσ

  have hS1 : (AddMonoidHom.toMultiplicativeRight (jDeg M M' H H' d A h φ)).comp
        (conjHom M H (⟨σ'.1, Gamma0_anti M M' h.dvd σ'.2⟩ : Gamma0 M))
      = ((AddMonoidHom.toMultiplicativeRight (pushChar M M' H H' d A h φ)).comp
          ((conjHom M H (⟨σ'.1, Gamma0_anti M M' h.dvd σ'.2⟩ : Gamma0 M)).subgroupComap
            (iotaDeg M M' H H' d h).range)).transfer := by
    ext k
    exact congrArg Multiplicative.toAdd
      (transfer_nat_inj (conjHom M H (⟨σ'.1, Gamma0_anti M M' h.dvd σ'.2⟩ : Gamma0 M))
        (AddMonoidHom.toMultiplicativeRight (pushChar M M' H H' d A h φ))
        (comapQuotientMap_conjHom_surjective _ _) k)

  have hS3 : MonoidHom.transfer (AddMonoidHom.toMultiplicativeRight
        (pushChar M M' H H' d A h (diamondRaw M' H' A σ' φ)))
      = ((AddMonoidHom.toMultiplicativeRight
            (pushChar M M' H H' d A h (diamondRaw M' H' A σ' φ))).comp
          ((conjHom M H ⟨(((innerComp σ' h)⁻¹ : ↥(GammaH M H)) : SL(2, ℤ)),
            GammaH_le_Gamma0 H ((innerComp σ' h)⁻¹).2⟩).subgroupComap
            (iotaDeg M M' H H' d h).range)).transfer := by
    have hd := comp_conjHom_of_mem
      (MonoidHom.transfer (AddMonoidHom.toMultiplicativeRight
        (pushChar M M' H H' d A h (diamondRaw M' H' A σ' φ)))) ((innerComp σ' h)⁻¹)
    rw [← hd]
    ext g
    exact congrArg Multiplicative.toAdd
      (transfer_nat_inj _ _ (comapQuotientMap_conjHom_surjective _ _) g)

  have hS5 : (AddMonoidHom.toMultiplicativeRight (pushChar M M' H H' d A h φ)).comp
        ((conjHom M H (⟨σ'.1, Gamma0_anti M M' h.dvd σ'.2⟩ : Gamma0 M)).subgroupComap
          (iotaDeg M M' H H' d h).range)
      = ((AddMonoidHom.toMultiplicativeRight
            (pushChar M M' H H' d A h (diamondRaw M' H' A σ' φ))).comp
          ((conjHom M H ⟨(((innerComp σ' h)⁻¹ : ↥(GammaH M H)) : SL(2, ℤ)),
            GammaH_le_Gamma0 H ((innerComp σ' h)⁻¹).2⟩).subgroupComap
            (iotaDeg M M' H H' d h).range)).comp
        (MulEquiv.subgroupCongr hsub).toMonoidHom := by
    refine MonoidHom.ext fun b => ?_
    have hbmem : conjHom M H ⟨(((innerComp σ' h)⁻¹ : ↥(GammaH M H)) : SL(2, ℤ)),
        GammaH_le_Gamma0 H ((innerComp σ' h)⁻¹).2⟩ (b : ↥(GammaH M H))
        ∈ (iotaDeg M M' H H' d h).range :=
      mem_comap.mp (hsub ▸ b.2)
    have hXY : (((iotaDeg M M' H H' d h).ofInjective
            (iotaDeg_injective M M' H H' d h)).symm
          ⟨conjHom M H (⟨σ'.1, Gamma0_anti M M' h.dvd σ'.2⟩ : Gamma0 M) (b : ↥(GammaH M H)),
            b.2⟩ : ↥(GammaH M' H'))
        = conjHom M' H' σ'
            (((iotaDeg M M' H H' d h).ofInjective (iotaDeg_injective M M' H H' d h)).symm
              ⟨conjHom M H ⟨(((innerComp σ' h)⁻¹ : ↥(GammaH M H)) : SL(2, ℤ)),
                GammaH_le_Gamma0 H ((innerComp σ' h)⁻¹).2⟩ (b : ↥(GammaH M H)), hbmem⟩) := by
      apply iotaDeg_injective M M' H H' d h
      rw [MonoidHom.apply_ofInjective_symm (iotaDeg_injective M M' H H' d h),
        conjHom_iotaDeg_eq M M' H H' d h σ',
        MonoidHom.apply_ofInjective_symm (iotaDeg_injective M M' H H' d h)]
      apply Subtype.ext
      push_cast [conjHom_apply_coe, innerComp]
      group
    exact congrArg (fun t => φ (Additive.ofMul t)) hXY

  have chain : (AddMonoidHom.toMultiplicativeRight (jDeg M M' H H' d A h φ)).comp
        (conjHom M H (⟨σ'.1, Gamma0_anti M M' h.dvd σ'.2⟩ : Gamma0 M))
      = MonoidHom.transfer (AddMonoidHom.toMultiplicativeRight
          (pushChar M M' H H' d A h (diamondRaw M' H' A σ' φ))) := by
    calc (AddMonoidHom.toMultiplicativeRight (jDeg M M' H H' d A h φ)).comp
          (conjHom M H (⟨σ'.1, Gamma0_anti M M' h.dvd σ'.2⟩ : Gamma0 M))
        = ((AddMonoidHom.toMultiplicativeRight (pushChar M M' H H' d A h φ)).comp
            ((conjHom M H (⟨σ'.1, Gamma0_anti M M' h.dvd σ'.2⟩ : Gamma0 M)).subgroupComap
              (iotaDeg M M' H H' d h).range)).transfer := hS1
      _ = (((AddMonoidHom.toMultiplicativeRight
              (pushChar M M' H H' d A h (diamondRaw M' H' A σ' φ))).comp
            ((conjHom M H ⟨(((innerComp σ' h)⁻¹ : ↥(GammaH M H)) : SL(2, ℤ)),
              GammaH_le_Gamma0 H ((innerComp σ' h)⁻¹).2⟩).subgroupComap
              (iotaDeg M M' H H' d h).range)).comp
          (MulEquiv.subgroupCongr hsub).toMonoidHom).transfer := by rw [hS5]
      _ = ((AddMonoidHom.toMultiplicativeRight
              (pushChar M M' H H' d A h (diamondRaw M' H' A σ' φ))).comp
            ((conjHom M H ⟨(((innerComp σ' h)⁻¹ : ↥(GammaH M H)) : SL(2, ℤ)),
              GammaH_le_Gamma0 H ((innerComp σ' h)⁻¹).2⟩).subgroupComap
              (iotaDeg M M' H H' d h).range)).transfer :=
          transfer_subgroupCongr hsub _
      _ = MonoidHom.transfer (AddMonoidHom.toMultiplicativeRight
            (pushChar M M' H H' d A h (diamondRaw M' H' A σ' φ))) := hS3.symm
  exact congrArg MonoidHom.toAdditiveLeft chain

end DEjD
end IharaMintJD

open IharaMintJD CohCarrier in
theorem solution {M M' : ℕ} {H : Subgroup (ZMod M)ˣ}
    {H' : Subgroup (ZMod M')ˣ} {d : ℕ} {A : Type} [AddCommGroup A] [NeZero d] [NeZero M']
    (σ : Gamma0 M) (hσ' : (σ : SL(2, ℤ)) ∈ Gamma0 M') (h : LevelLE M M' H H' d)
    (φ : H1 M' H' A) :
    diamondRaw M H A σ (jDeg M M' H H' d A h φ)
      = jDeg M M' H H' d A h (diamondRaw M' H' A ⟨↑σ, hσ'⟩ φ) :=
  jDeg_diamond_intertwine_impl (⟨↑σ, hσ'⟩ : Gamma0 M') h φ

end S_CohCarrier_jDeg_diamondRaw_comm
end P2MW
export P2MW.S_CohCarrier_jDeg_diamondRaw_comm (solution)
