-- Prove2me | solution 1 for CohCarrier.jDeg_heckeT_comm_flat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/0a6b4827-2714-5191-8899-34eb761f0634

import Definitions.Def_CohCarrier_Level
import Mathlib.Algebra.Field.ZMod
import Mathlib.GroupTheory.QuotientGroup.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_jDeg_heckeT_comm_flat

set_option autoImplicit false
open scoped MatrixGroups
open Subgroup Subgroup.leftTransversals CohCarrier CongruenceSubgroup

namespace IharaMintJT

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

section SL2Gen
variable {F : Type*} [Field F]

def E12 (x : F) : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, x; 0, 1], by simp [Matrix.det_fin_two_of]⟩
def E21 (y : F) : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, 0; y, 1], by simp [Matrix.det_fin_two_of]⟩

theorem SL2_decomp_of_ne (M : Matrix.SpecialLinearGroup (Fin 2) F) (hc : M.1 1 0 ≠ 0) :
    M = E12 ((M.1 0 0 - 1) / M.1 1 0) * E21 (M.1 1 0) * E12 ((M.1 1 1 - 1) / M.1 1 0) := by
  have hdet : M.1 0 0 * M.1 1 1 - M.1 0 1 * M.1 1 0 = 1 := by
    rw [← Matrix.det_fin_two]; exact M.2
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;>
    simp [E12, E21, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp
  · ring
  · linear_combination (-1 : F) * hdet
  · ring

theorem subgroup_eq_top_of_elementary (H : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))
    (h12 : ∀ x, E12 x ∈ H) (h21 : ∀ y, E21 y ∈ H) : H = ⊤ := by
  rw [eq_top_iff]
  rintro M -
  by_cases hc : M.1 1 0 = 0
  · have hdet : M.1 0 0 * M.1 1 1 - M.1 0 1 * M.1 1 0 = 1 := by
      rw [← Matrix.det_fin_two]; exact M.2
    have ha : M.1 0 0 ≠ 0 := by
      intro ha; rw [ha, hc] at hdet; simp at hdet
    set M' := E21 (1 : F) * M with hM'
    have hc' : M'.1 1 0 ≠ 0 := by
      have : M'.1 1 0 = M.1 0 0 + M.1 1 0 := by
        rw [hM', Matrix.SpecialLinearGroup.coe_mul]
        simp [E21, Matrix.mul_apply, Fin.sum_univ_two]
      rw [this, hc, add_zero]; exact ha
    have hmem : M' ∈ H := by
      rw [SL2_decomp_of_ne M' hc']
      exact H.mul_mem (H.mul_mem (h12 _) (h21 _)) (h12 _)
    rw [← inv_mul_cancel_left (E21 (1 : F)) M]
    exact H.mul_mem (H.inv_mem (h21 1)) hmem
  · rw [SL2_decomp_of_ne M hc]
    exact H.mul_mem (H.mul_mem (h12 _) (h21 _)) (h12 _)

end SL2Gen

abbrev redq (q : ℕ) : SL(2, ℤ) →* Matrix.SpecialLinearGroup (Fin 2) (ZMod q) :=
  Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q))

theorem redq_apply (q : ℕ) (γ : SL(2, ℤ)) (i j : Fin 2) :
    (redq q γ).1 i j = ((γ i j : ℤ) : ZMod q) := rfl

variable {G : Type*} [Group G] {C : Type*} [CommGroup C]

theorem prodRep_section (K L : Subgroup G) (hKL : K ≤ L) (q : G ⧸ K) :
    ((Quotient.out (Subgroup.quotientEquivProdOfLE hKL q).1
      * ((Quotient.out (Subgroup.quotientEquivProdOfLE hKL q).2 : L) : G) : G) : G ⧸ K) = q := by
  conv_rhs => rw [← (Subgroup.quotientEquivProdOfLE hKL).symm_apply_apply q]
  rw [show (Subgroup.quotientEquivProdOfLE hKL) q
      = ((Subgroup.quotientEquivProdOfLE hKL q).1, (Subgroup.quotientEquivProdOfLE hKL q).2)
    from rfl, Subgroup.quotientEquivProdOfLE_symm_apply]
  conv_rhs => rw [← Quotient.out_eq' (Subgroup.quotientEquivProdOfLE hKL q).2, Quotient.map'_mk'']

theorem quotientEquivProdOfLE_smul (K L : Subgroup G) (hKL : K ≤ L)
    [L.FiniteIndex] (g : G) (q : G ⧸ K) :
    (Subgroup.quotientEquivProdOfLE hKL (g⁻¹ • q)).1
      = g⁻¹ • (Subgroup.quotientEquivProdOfLE hKL q).1 := by
  induction q using Quotient.inductionOn' with
  | h a =>
    simp only [Subgroup.quotientEquivProdOfLE, Subgroup.quotientEquivProdOfLE'_apply,
      Quotient.map'_mk'', id]
    rfl

theorem diffElt_mem_aux (L : Subgroup G) (g : G) (p : G ⧸ L) :
    (Quotient.out p)⁻¹ * (g * Quotient.out (g⁻¹ • p : G ⧸ L)) ∈ L := by
  refine QuotientGroup.leftRel_apply.mp (Quotient.exact' ?_)
  rw [Quotient.out_eq', ← smul_eq_mul]
  conv_lhs => rw [← smul_inv_smul g p]
  exact (MulAction.Quotient.mk_smul_out (G := G) (X := G) (H := L) g (g⁻¹ • p)).symm

noncomputable def diffElt (L : Subgroup G) (g : G) (p : G ⧸ L) : L :=
  ⟨(Quotient.out p)⁻¹ * (g * Quotient.out (g⁻¹ • p : G ⧸ L)), diffElt_mem_aux L g p⟩

theorem diffElt_coe (L : Subgroup G) (g : G) (p : G ⧸ L) :
    (diffElt L g p : G) = (Quotient.out p)⁻¹ * (g * Quotient.out (g⁻¹ • p : G ⧸ L)) := rfl

theorem quotientEquivProdOfLE_smul_snd (K L : Subgroup G) (hKL : K ≤ L) (g : G) (q : G ⧸ K) :
    (Subgroup.quotientEquivProdOfLE hKL (g⁻¹ • q)).2
      = (diffElt L g (Subgroup.quotientEquivProdOfLE hKL q).1)⁻¹
          • (Subgroup.quotientEquivProdOfLE hKL q).2 := by
  induction q using Quotient.inductionOn' with
  | _ a =>
  set p : G ⧸ L := Quotient.mk'' a with hp
  have h1 : (Subgroup.quotientEquivProdOfLE hKL (Quotient.mk'' a)).1 = p := by
    simp only [Subgroup.quotientEquivProdOfLE, Subgroup.quotientEquivProdOfLE'_apply,
      Quotient.map'_mk'', id, hp]
  rw [h1]
  simp only [Subgroup.quotientEquivProdOfLE, Subgroup.quotientEquivProdOfLE'_apply,
    MulAction.Quotient.smul_mk, Quotient.map'_mk'', id, smul_eq_mul]
  refine congrArg Quotient.mk'' (Subtype.ext ?_)
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, diffElt_coe, _root_.mul_inv_rev, inv_inv]
  have hL : (Quotient.mk'' (g⁻¹ * a) : G ⧸ L) = g⁻¹ • p := by
    rw [hp, ← smul_eq_mul]; exact (MulAction.Quotient.smul_mk (H := L) g⁻¹ a).symm
  rw [hL, ← hp]
  group

theorem transfer_transitive {G : Type*} [Group G] {C : Type*} [CommGroup C]
    (K L : Subgroup G) (hKL : K ≤ L)
    [K.FiniteIndex] [L.FiniteIndex] [(K.subgroupOf L).FiniteIndex] (ψ : K →* C) :
    MonoidHom.transfer ψ
      = MonoidHom.transfer
          (MonoidHom.transfer (ψ.comp (Subgroup.subgroupOfEquivOfLe hKL).toMonoidHom)) := by
  classical
  ext g
  letI := K.fintypeQuotientOfFiniteIndex
  letI := L.fintypeQuotientOfFiniteIndex
  letI := (K.subgroupOf L).fintypeQuotientOfFiniteIndex
  set ψ' := ψ.comp (Subgroup.subgroupOfEquivOfLe hKL).toMonoidHom
  set prodT : K.LeftTransversal := ⟨_, Subgroup.isComplement_range_left (prodRep_section K L hKL)⟩
  rw [MonoidHom.transfer_def ψ prodT, MonoidHom.transfer_def ψ'.transfer default,
    Subgroup.leftTransversals.diff, Subgroup.leftTransversals.diff]
  simp only [Subgroup.smul_apply_eq_smul_apply_inv_smul,
    Subgroup.IsComplement.leftQuotientEquiv_apply (prodRep_section K L hKL),
    Subgroup.IsComplement.leftQuotientEquiv_apply Quotient.out_eq', smul_eq_mul]
  rw [← Equiv.prod_comp (Subgroup.quotientEquivProdOfLE hKL).symm]
  simp_rw [MonoidHom.transfer_def ψ' default, Subgroup.leftTransversals.diff,
    Subgroup.smul_apply_eq_smul_apply_inv_smul,
    Subgroup.IsComplement.leftQuotientEquiv_apply Quotient.out_eq', smul_eq_mul]
  rw [← Finset.prod_product', Finset.univ_product_univ]
  refine Finset.prod_congr rfl fun x _ => ?_
  obtain ⟨p, r⟩ := x
  simp only [quotientEquivProdOfLE_smul K L hKL, quotientEquivProdOfLE_smul_snd K L hKL,
    Equiv.apply_symm_apply, diffElt]
  simp only [ψ', MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe]
  congr 1
  refine Subtype.ext ?_
  simp only [Subgroup.subgroupOfEquivOfLe_apply_coe, Subgroup.coe_mul, Subgroup.coe_inv,
    _root_.mul_inv_rev]
  group

section DejT
variable {M M' : ℕ} {H : Subgroup (ZMod M)ˣ} {H' : Subgroup (ZMod M')ˣ} {d ℓ : ℕ}
  {A : Type} [AddCommGroup A]

theorem conjL_subgroupComap_iotaDeg [NeZero d] [NeZero M'] [NeZero ℓ]
    (h : LevelLE M M' H H' d) (hℓd : ℓ.Coprime d)
    (k : ↥((GammaHUpper M H ℓ).comap (iotaDeg M M' H H' d h))) :
    conjL M H ℓ (((iotaDeg M M' H H' d h).subgroupComap (GammaHUpper M H ℓ)) k)
      = iotaDeg M M' H H' d h (conjL M' H' ℓ
          ⟨(k : ↥(GammaH M' H')),
            comap_GammaHUpper_iotaDeg h hℓd ▸ k.2⟩) := by
  have hℓX : (ℓ : ℤ) ∣ ((k : ↥(GammaH M' H')) : SL(2, ℤ)) 0 1 :=
    dvd_of_mem_GammaHUpper M' H' ℓ
      ⟨(k : ↥(GammaH M' H')), comap_GammaHUpper_iotaDeg h hℓd ▸ k.2⟩
  have hdX : (d : ℤ) ∣ ((k : ↥(GammaH M' H')) : SL(2, ℤ)) 1 0 :=
    h.dvd_entry (k : ↥(GammaH M' H'))
  have hℓ' : (ℓ : ℤ) ∣
      (conjLowerMat d ((k : ↥(GammaH M' H')) : SL(2, ℤ)) hdX : SL(2, ℤ)) 0 1 := by
    rw [conjLowerMat_01]; exact hℓX.mul_right _
  have hd' : (d : ℤ) ∣
      (conjUpperMat ℓ ((k : ↥(GammaH M' H')) : SL(2, ℤ)) hℓX : SL(2, ℤ)) 1 0 := by
    rw [conjUpperMat_apply_10]; exact hdX.mul_right _
  exact Subtype.ext (conjUpperMat_conjLowerMat_comm _ hℓX hdX hℓ' hd')

theorem conjL_mem_range_iotaDeg_iff_proved [NeZero d] [NeZero M'] [NeZero ℓ]
    (h : LevelLE M M' H H' d) (hℓd : ℓ.Coprime d) (hℓ : ℓ.Prime) (hℓM' : ¬ ℓ ∣ M')
    (k : ↥(GammaHUpper M H ℓ)) :
    conjL M H ℓ k ∈ (iotaDeg M M' H H' d h).range
      ↔ (k : ↥(GammaH M H)) ∈ (iotaDeg M M' H H' d h).range := by
  constructor
  ·
    rintro ⟨γ₀, hγ₀⟩
    set X : SL(2, ℤ) := ((k : ↥(GammaH M H)) : SL(2, ℤ)) with hXdef
    set Y : SL(2, ℤ) := ((γ₀ : ↥(GammaH M' H')) : SL(2, ℤ)) with hYdef
    have hbX0 : (ℓ : ℤ) ∣ X 0 1 := dvd_of_mem_GammaHUpper M H ℓ k
    have hdY : (d : ℤ) ∣ Y 1 0 := h.dvd_entry _
    have hXY : conjLowerMat d Y hdY = conjUpperMat ℓ X hbX0 :=
      congrArg (fun z : ↥(GammaH M H) => (z : SL(2, ℤ))) hγ₀
    have hE : ∀ i j, (conjLowerMat d Y hdY : SL(2, ℤ)) i j
        = (conjUpperMat ℓ X hbX0 : SL(2, ℤ)) i j := fun i j => by rw [hXY]
    have h01 : Y 0 1 * d = X 0 1 / ℓ := by
      have := hE 0 1; simpa [conjLowerMat, conjUpperMat, Matrix.of_apply] using this
    have h10 : Y 1 0 / d = X 1 0 * ℓ := by
      have := hE 1 0; simpa [conjLowerMat, conjUpperMat, Matrix.of_apply] using this
    have h00 : Y 0 0 = X 0 0 := by
      have := hE 0 0; simpa [conjLowerMat, conjUpperMat, Matrix.of_apply] using this
    have h11 : Y 1 1 = X 1 1 := by
      have := hE 1 1; simpa [conjLowerMat, conjUpperMat, Matrix.of_apply] using this
    have hbXexact : X 0 1 = ℓ * (Y 0 1 * d) := by
      rw [h01]; exact (Int.mul_ediv_cancel' hbX0).symm
    have hdbX : (d : ℤ) ∣ X 0 1 := ⟨ℓ * Y 0 1, by rw [hbXexact]; ring⟩
    have hcYexact : Y 1 0 = X 1 0 * ℓ * d := by
      have := Int.ediv_mul_cancel hdY
      rw [h10] at this; linarith [this]

    obtain ⟨hY0, hYH⟩ := mem_GammaH_iff.mp (γ₀ : ↥(GammaH M' H')).2
    have hcY : ((M' : ℕ) : ℤ) ∣ Y 1 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hY0)
    have hcopN : Nat.Coprime M' ℓ := ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM').symm
    have hcop : IsCoprime ((M' : ℕ) : ℤ) (ℓ : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
      exact hcopN
    have hM'cd : ((M' : ℕ) : ℤ) ∣ X 1 0 * d :=
      hcop.dvd_of_dvd_mul_right (by rw [show X 1 0 * d * ℓ = X 1 0 * ℓ * d by ring, ← hcYexact]; exact hcY)
    have hδ0 : conjUpperMat d X hdbX ∈ Gamma0 M' := by
      rw [Gamma0_mem, conjUpperMat_apply_10, Int.cast_mul]
      have : ((X 1 0 * d : ℤ) : ZMod M') = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hM'cd
      rwa [Int.cast_mul] at this
    have hδmem : conjUpperMat d X hdbX ∈ GammaH M' H' := by
      rw [mem_GammaH_iff]
      refine ⟨hδ0, ?_⟩
      have : gamma0Units M' ⟨conjUpperMat d X hdbX, hδ0⟩ = gamma0Units M' ⟨Y, hY0⟩ := by
        ext
        simp [gamma0Units, Gamma0Map, conjUpperMat, Matrix.of_apply, h11]
      rw [this]; exact hYH
    refine ⟨⟨conjUpperMat d X hdbX, hδmem⟩, ?_⟩

    apply Subtype.ext
    show conjLowerMat d (conjUpperMat d X hdbX)
        (h.dvd_entry ⟨conjUpperMat d X hdbX, hδmem⟩) = X
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [conjLowerMat, conjUpperMat, Matrix.of_apply, Int.ediv_mul_cancel hdbX]
    exact Int.mul_ediv_cancel _ (by exact_mod_cast (NeZero.ne d : d ≠ 0))
  ·
    rintro ⟨γ', hγ'⟩
    have hup : γ' ∈ (GammaHUpper M H ℓ).comap (iotaDeg M M' H H' d h) := by
      rw [mem_comap, hγ']; exact k.2
    have hsq := conjL_subgroupComap_iotaDeg h hℓd ⟨γ', hup⟩
    have hk : ((iotaDeg M M' H H' d h).subgroupComap (GammaHUpper M H ℓ)) ⟨γ', hup⟩ = k :=
      Subtype.ext hγ'
    rw [hk] at hsq
    exact ⟨_, hsq.symm⟩

theorem ofInjective_symm_mem_upper [NeZero d] [NeZero M'] [NeZero ℓ]
    (h : LevelLE M M' H H' d) (hℓd : ℓ.Coprime d)
    (k : ↥(GammaHUpper M H ℓ)) (hr : (k : ↥(GammaH M H)) ∈ (iotaDeg M M' H H' d h).range) :
    (((iotaDeg M M' H H' d h).ofInjective (iotaDeg_injective M M' H H' d h)).symm
        ⟨(k : ↥(GammaH M H)), hr⟩ : ↥(GammaH M' H')) ∈ GammaHUpper M' H' ℓ := by
  rw [← comap_GammaHUpper_iotaDeg h hℓd, mem_comap,
    MonoidHom.apply_ofInjective_symm (iotaDeg_injective M M' H H' d h)]
  exact k.2

theorem pushChar_conjL_eq_proved [NeZero d] [NeZero M'] [NeZero ℓ]
    (h : LevelLE M M' H H' d) (hℓd : ℓ.Coprime d) (hℓ : ℓ.Prime) (hℓM' : ¬ ℓ ∣ M')
    (φ : H1 M' H' A) (k : ↥(GammaHUpper M H ℓ))
    (hk : conjL M H ℓ k ∈ (iotaDeg M M' H H' d h).range) :
    pushChar M M' H H' d A h φ (Additive.ofMul ⟨conjL M H ℓ k, hk⟩)
      = φ (Additive.ofMul (conjL M' H' ℓ
          ⟨((iotaDeg M M' H H' d h).ofInjective (iotaDeg_injective M M' H H' d h)).symm
              ⟨(k : ↥(GammaH M H)), (conjL_mem_range_iotaDeg_iff_proved h hℓd hℓ hℓM' k).mp hk⟩,
            ofInjective_symm_mem_upper h hℓd k
              ((conjL_mem_range_iotaDeg_iff_proved h hℓd hℓ hℓM' k).mp hk)⟩)) := by
  set hr := (conjL_mem_range_iotaDeg_iff_proved h hℓd hℓ hℓM' k).mp hk with hrdef
  set γ' : ↥(GammaH M' H') :=
    ((iotaDeg M M' H H' d h).ofInjective (iotaDeg_injective M M' H H' d h)).symm
      ⟨(k : ↥(GammaH M H)), hr⟩ with hγ'def
  have hγ'up : γ' ∈ GammaHUpper M' H' ℓ := ofInjective_symm_mem_upper h hℓd k hr

  have hu : (((iotaDeg M M' H H' d h).ofInjective (iotaDeg_injective M M' H H' d h)).symm
        ⟨conjL M H ℓ k, hk⟩ : ↥(GammaH M' H'))
      = conjL M' H' ℓ ⟨γ', hγ'up⟩ := by
    apply iotaDeg_injective M M' H H' d h
    rw [MonoidHom.apply_ofInjective_symm (iotaDeg_injective M M' H H' d h)]

    have hιγ' : iotaDeg M M' H H' d h γ' = (k : ↥(GammaH M H)) :=
      MonoidHom.apply_ofInjective_symm (iotaDeg_injective M M' H H' d h) _
    have hup : γ' ∈ (GammaHUpper M H ℓ).comap (iotaDeg M M' H H' d h) := by
      rw [mem_comap, hιγ']; exact k.2
    have hsq := conjL_subgroupComap_iotaDeg h hℓd ⟨γ', hup⟩
    have hkk : ((iotaDeg M M' H H' d h).subgroupComap (GammaHUpper M H ℓ)) ⟨γ', hup⟩ = k :=
      Subtype.ext hιγ'
    rw [hkk] at hsq
    exact hsq
  show φ ((MonoidHom.toAdditive
      ((iotaDeg M M' H H' d h).ofInjective (iotaDeg_injective M M' H H' d h)).symm.toMonoidHom)
      (Additive.ofMul ⟨conjL M H ℓ k, hk⟩)) = _
  exact congrArg φ (congrArg Additive.ofMul hu)

theorem comap_conjL_range_iotaDeg [NeZero d] [NeZero M'] [NeZero ℓ]
    (h : LevelLE M M' H H' d) (hℓd : ℓ.Coprime d) (hℓ : ℓ.Prime) (hℓM' : ¬ ℓ ∣ M') :
    (iotaDeg M M' H H' d h).range.comap (conjL M H ℓ)
      = (iotaDeg M M' H H' d h).range.comap (GammaHUpper M H ℓ).subtype := by
  ext k
  rw [Subgroup.mem_comap, Subgroup.mem_comap]
  exact conjL_mem_range_iotaDeg_iff_proved h hℓd hℓ hℓM' k

section FlatCov

theorem redq_Gamma_surjective (n ℓ : ℕ) (hq : ℓ.Prime) (hqn : ¬ ℓ ∣ n) :
    Function.Surjective ((redq ℓ).comp (Gamma n).subtype) := by
  haveI : Fact ℓ.Prime := ⟨hq⟩
  have hn' : ((n : ℕ) : ZMod ℓ) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; exact hqn
  rw [← MonoidHom.range_eq_top]
  apply subgroup_eq_top_of_elementary
  · intro x
    let s : ℤ := ((((n : ℕ) : ZMod ℓ))⁻¹ * x).val
    let γsl : SL(2, ℤ) := ⟨!![1, (n : ℤ) * s; 0, 1], by simp [Matrix.det_fin_two_of]⟩
    have hγ : γsl ∈ Gamma n := by
      rw [Gamma_mem]
      refine ⟨?_, ?_, ?_, ?_⟩
      · show ((1 : ℤ) : ZMod n) = 1; exact Int.cast_one
      · show (((n : ℤ) * s : ℤ) : ZMod n) = 0
        push_cast; rw [ZMod.natCast_self, zero_mul]
      · show ((0 : ℤ) : ZMod n) = 0; exact Int.cast_zero
      · show ((1 : ℤ) : ZMod n) = 1; exact Int.cast_one
    refine ⟨⟨γsl, hγ⟩, ?_⟩
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    show (redq ℓ γsl).1 i j = (E12 x).1 i j
    rw [redq_apply]
    fin_cases i <;> fin_cases j <;>
      simp [γsl, s, E12, mul_inv_cancel_left₀ hn']
  · intro y
    let t : ℤ := ((((n : ℕ) : ZMod ℓ))⁻¹ * y).val
    let γsl : SL(2, ℤ) := ⟨!![1, 0; (n : ℤ) * t, 1], by simp [Matrix.det_fin_two_of]⟩
    have hγ : γsl ∈ Gamma n := by
      rw [Gamma_mem]
      refine ⟨?_, ?_, ?_, ?_⟩
      · show ((1 : ℤ) : ZMod n) = 1; exact Int.cast_one
      · show ((0 : ℤ) : ZMod n) = 0; exact Int.cast_zero
      · show (((n : ℤ) * t : ℤ) : ZMod n) = 0
        push_cast; rw [ZMod.natCast_self, zero_mul]
      · show ((1 : ℤ) : ZMod n) = 1; exact Int.cast_one
    refine ⟨⟨γsl, hγ⟩, ?_⟩
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    show (redq ℓ γsl).1 i j = (E21 y).1 i j
    rw [redq_apply]
    fin_cases i <;> fin_cases j <;>
      simp [γsl, t, E21, mul_inv_cancel_left₀ hn']

variable {ℓ : ℕ}

theorem comapQuotientMap_subtype_surjective [NeZero M'] [NeZero d]
    (h : LevelLE M M' H H' d) (hℓd : ℓ.Coprime d) (hℓ : ℓ.Prime) (hℓM' : ¬ ℓ ∣ M') :
    Function.Surjective (comapQuotientMap ((GammaHUpper M H ℓ).subtype)
      (iotaDeg M M' H H' d h).range) := by
  haveI : NeZero (M' * d) := ⟨mul_ne_zero (NeZero.ne M') (NeZero.ne d)⟩
  have hℓMd : ¬ ℓ ∣ (M' * d) := by
    rw [hℓ.dvd_mul]
    rintro (hM' | hd)
    · exact hℓM' hM'
    · exact (Nat.Prime.coprime_iff_not_dvd hℓ).mp hℓd hd
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨⟨k₀, hk₀Γ⟩, hk₀red⟩ :=
    redq_Gamma_surjective (M' * d) ℓ hℓ hℓMd ((redq ℓ (g : SL(2, ℤ)))⁻¹)
  have hr : redq ℓ k₀ = (redq ℓ (g : SL(2, ℤ)))⁻¹ := hk₀red

  have hMd : (M : ℕ) ∣ M' * d := dvd_mul_of_dvd_left h.dvd d
  obtain ⟨h00, h01, h10, h11⟩ := Gamma_mem.mp hk₀Γ
  have hc : ((k₀ 1 0 : ℤ) : ZMod M) = 0 := by
    rw [← map_intCast (ZMod.castHom hMd (ZMod M)) (k₀ 1 0), h10, map_zero]
  have hd11 : ((k₀ 1 1 : ℤ) : ZMod M) = 1 := by
    rw [← map_intCast (ZMod.castHom hMd (ZMod M)) (k₀ 1 1), h11, map_one]
  have hk₀G0 : k₀ ∈ Gamma0 M := by rw [Gamma0_mem]; exact hc
  have hk₀H : k₀ ∈ GammaH M H := by
    refine mem_GammaH_iff.mpr ⟨hk₀G0, ?_⟩
    have e : gamma0Units M ⟨k₀, hk₀G0⟩ = 1 := by
      apply Units.ext
      rw [val_gamma0Units, Units.val_one]
      show ((k₀ 1 1 : ℤ) : ZMod M) = 1
      exact hd11
    rw [e]; exact H.one_mem
  set kH : ↥(GammaH M H) := ⟨k₀, hk₀H⟩ with hkH

  have hred : redq ℓ ((g * kH : ↥(GammaH M H)) : SL(2, ℤ)) = 1 := by
    rw [Subgroup.coe_mul, map_mul, hkH]
    show redq ℓ (g : SL(2, ℤ)) * redq ℓ k₀ = 1
    rw [hr, mul_inv_cancel]
  have hkU : (g * kH : ↥(GammaH M H)) ∈ GammaHUpper M H ℓ := by
    show ((g * kH : ↥(GammaH M H)) : SL(2, ℤ)) ∈ Gamma0Upper ℓ
    rw [mem_Gamma0Upper, ← redq_apply, hred]
    simp

  have hk₀range : kH ∈ (iotaDeg M M' H H' d h).range := by
    apply Gamma_subgroupOf_le_range_iotaDeg M M' H H' d h
    rw [Subgroup.mem_subgroupOf]
    exact hk₀Γ
  refine ⟨((⟨g * kH, hkU⟩ : ↥(GammaHUpper M H ℓ)) : ↥(GammaHUpper M H ℓ) ⧸ _), ?_⟩
  rw [comapQuotientMap_mk, QuotientGroup.eq]
  show ((g * kH)⁻¹ * g) ∈ (iotaDeg M M' H H' d h).range
  have e : (g * kH)⁻¹ * g = kH⁻¹ := by group
  rw [e]
  exact inv_mem hk₀range

theorem index_comap_conjL_range_iotaDeg_proved [NeZero d] [NeZero M'] [NeZero ℓ]
    (h : LevelLE M M' H H' d) (hℓd : ℓ.Coprime d) (hℓ : ℓ.Prime) (hℓM' : ¬ ℓ ∣ M') :
    ((iotaDeg M M' H H' d h).range.comap (conjL M H ℓ)).index
      = (iotaDeg M M' H H' d h).range.index := by
  rw [comap_conjL_range_iotaDeg h hℓd hℓ hℓM']
  show Nat.card _ = Nat.card _
  exact Nat.card_eq_of_bijective _
    ⟨comapQuotientMap_injective _ _, comapQuotientMap_subtype_surjective h hℓd hℓ hℓM'⟩

theorem iotaDeg_comp_ofInjectiveSymm [NeZero d] [NeZero M'] (h : LevelLE M M' H H' d) :
    (iotaDeg M M' H H' d h).comp
        (((iotaDeg M M' H H' d h).ofInjective (iotaDeg_injective M M' H H' d h)).symm.toMonoidHom)
      = (iotaDeg M M' H H' d h).range.subtype := by
  refine MonoidHom.ext fun r => ?_
  show (iotaDeg M M' H H' d h)
      (((iotaDeg M M' H H' d h).ofInjective (iotaDeg_injective M M' H H' d h)).symm r)
    = (r : ↥(GammaH M H))
  exact MonoidHom.apply_ofInjective_symm (iotaDeg_injective M M' H H' d h) r

theorem comap_ofInjectiveSymm_upper [NeZero d] [NeZero M'] [NeZero ℓ]
    (h : LevelLE M M' H H' d) (hℓd : ℓ.Coprime d) :
    (GammaHUpper M' H' ℓ).comap
        (((iotaDeg M M' H H' d h).ofInjective (iotaDeg_injective M M' H H' d h)).symm.toMonoidHom)
      = ((iotaDeg M M' H H' d h).range ⊓ GammaHUpper M H ℓ).subgroupOf
          (iotaDeg M M' H H' d h).range := by
  rw [← comap_GammaHUpper_iotaDeg h hℓd, Subgroup.comap_comap,
    iotaDeg_comp_ofInjectiveSymm h, inf_subgroupOf_left]
  rfl

theorem transfer_transfer_eq {G : Type*} [Group G] {C : Type*} [CommGroup C]
    (K L : Subgroup G) (hKL : K ≤ L) [K.FiniteIndex] [L.FiniteIndex]
    [(K.subgroupOf L).FiniteIndex] (χ : ↥(K.subgroupOf L) →* C) :
    MonoidHom.transfer (MonoidHom.transfer χ)
      = MonoidHom.transfer (χ.comp (Subgroup.subgroupOfEquivOfLe hKL).symm.toMonoidHom) := by
  have htrans := transfer_transitive K L hKL
    (χ.comp (Subgroup.subgroupOfEquivOfLe hKL).symm.toMonoidHom)
  have hcancel : ((χ.comp (Subgroup.subgroupOfEquivOfLe hKL).symm.toMonoidHom).comp
      (Subgroup.subgroupOfEquivOfLe hKL).toMonoidHom) = χ := by
    ext x
    simp
  rw [hcancel] at htrans
  exact htrans.symm

end FlatCov
end DejT
end IharaMintJT
p2m_reactivate "P2MW.S_CohCarrier_jDeg_heckeT_comm_flat.IharaMintJT"

open CohCarrier IharaMintJT in
theorem solution {M M' : ℕ} {H : Subgroup (ZMod M)ˣ} {H' : Subgroup (ZMod M')ˣ} {d ℓ : ℕ}
    {A : Type} [AddCommGroup A] [NeZero d] [NeZero M'] [NeZero ℓ]
    (h : LevelLE M M' H H' d) (hℓd : ℓ.Coprime d) (hℓ : ℓ.Prime)
    (hℓM' : ¬ ℓ ∣ M') (φ : H1 M' H' A) :
    heckeT M H ℓ A (jDeg M M' H H' d A h φ)
      = jDeg M M' H H' d A h (heckeT M' H' ℓ A φ) := by
  classical

  have hEq : ((iotaDeg M M' H H' d h).range ⊓ GammaHUpper M H ℓ).subgroupOf (GammaHUpper M H ℓ)
      = (iotaDeg M M' H H' d h).range.comap (conjL M H ℓ) := by
    rw [inf_subgroupOf_right]
    exact (comap_conjL_range_iotaDeg h hℓd hℓ hℓM').symm
  have hEq' := comap_ofInjectiveSymm_upper h hℓd

  have hidx := index_comap_conjL_range_iotaDeg_proved h hℓd hℓ hℓM'
  haveI hCfi : ((iotaDeg M M' H H' d h).range.comap (conjL M H ℓ)).FiniteIndex := ⟨by
    rw [hidx]
    exact Subgroup.FiniteIndex.index_ne_zero⟩

  have hsurjL : Function.Surjective
      (comapQuotientMap (conjL M H ℓ) (iotaDeg M M' H H' d h).range) :=
    comapQuotientMap_surjective_of_index_eq _ _ hidx

  have hsurjR : Function.Surjective (comapQuotientMap
      (((iotaDeg M M' H H' d h).ofInjective (iotaDeg_injective M M' H H' d h)).symm.toMonoidHom)
      (GammaHUpper M' H' ℓ)) := by
    intro q
    obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨((((iotaDeg M M' H H' d h).ofInjective (iotaDeg_injective M M' H H' d h)) g'
        : ↥(iotaDeg M M' H H' d h).range) : _ ⧸ _), ?_⟩
    rw [comapQuotientMap_mk]
    congr 1
    exact MulEquiv.symm_apply_apply _ g'
  have hidx' : ((GammaHUpper M' H' ℓ).comap
        (((iotaDeg M M' H H' d h).ofInjective (iotaDeg_injective M M' H H' d h)).symm.toMonoidHom)).index
      = (GammaHUpper M' H' ℓ).index :=
    Nat.card_eq_of_bijective _ ⟨comapQuotientMap_injective _ _, hsurjR⟩
  haveI hKfi' : ((GammaHUpper M' H' ℓ).comap
      (((iotaDeg M M' H H' d h).ofInjective (iotaDeg_injective M M' H H' d h)).symm.toMonoidHom)).FiniteIndex :=
    ⟨by rw [hidx']; exact Subgroup.FiniteIndex.index_ne_zero⟩

  set χ₂ := (AddMonoidHom.toMultiplicativeRight (pushChar M M' H H' d A h φ)).comp
    ((conjL M H ℓ).subgroupComap (iotaDeg M M' H H' d h).range) with hχ₂def
  set χ₂R := ((AddMonoidHom.toMultiplicativeRight φ).comp (conjL M' H' ℓ)).comp
    ((((iotaDeg M M' H H' d h).ofInjective (iotaDeg_injective M M' H H' d h)).symm.toMonoidHom).subgroupComap
      (GammaHUpper M' H' ℓ)) with hχ₂Rdef

  have hS1 : (AddMonoidHom.toMultiplicativeRight (jDeg M M' H H' d A h φ)).comp (conjL M H ℓ)
      = χ₂.transfer := by
    ext k
    exact congrArg Multiplicative.toAdd
      (transfer_nat_inj (conjL M H ℓ)
        (AddMonoidHom.toMultiplicativeRight (pushChar M M' H H' d A h φ)) hsurjL k)
  have hS3 : AddMonoidHom.toMultiplicativeRight
        (pushChar M M' H H' d A h (heckeT M' H' ℓ A φ))
      = χ₂R.transfer := by
    ext r
    exact congrArg Multiplicative.toAdd
      (transfer_nat_inj
        (((iotaDeg M M' H H' d h).ofInjective (iotaDeg_injective M M' H H' d h)).symm.toMonoidHom)
        ((AddMonoidHom.toMultiplicativeRight φ).comp (conjL M' H' ℓ)) hsurjR r)

  have hS5 : (χ₂.comp (MulEquiv.subgroupCongr hEq).toMonoidHom).comp
        (Subgroup.subgroupOfEquivOfLe
          (inf_le_right : (iotaDeg M M' H H' d h).range ⊓ GammaHUpper M H ℓ ≤ GammaHUpper M H ℓ)).symm.toMonoidHom
      = (χ₂R.comp (MulEquiv.subgroupCongr hEq'.symm).toMonoidHom).comp
        (Subgroup.subgroupOfEquivOfLe
          (inf_le_left : (iotaDeg M M' H H' d h).range ⊓ GammaHUpper M H ℓ ≤ (iotaDeg M M' H H' d h).range)).symm.toMonoidHom := by
    ext b
    exact congrArg Multiplicative.toAdd
      (pushChar_conjL_eq_proved h hℓd hℓ hℓM' φ ⟨(b : ↥(GammaH M H)), b.2.2⟩
        ((conjL_mem_range_iotaDeg_iff_proved h hℓd hℓ hℓM'
          ⟨(b : ↥(GammaH M H)), b.2.2⟩).mpr b.2.1))

  have chain : MonoidHom.transfer
        ((AddMonoidHom.toMultiplicativeRight (jDeg M M' H H' d A h φ)).comp (conjL M H ℓ))
      = MonoidHom.transfer (AddMonoidHom.toMultiplicativeRight
          (pushChar M M' H H' d A h (heckeT M' H' ℓ A φ))) := by
    calc MonoidHom.transfer
          ((AddMonoidHom.toMultiplicativeRight (jDeg M M' H H' d A h φ)).comp (conjL M H ℓ))
        = MonoidHom.transfer χ₂.transfer := by rw [hS1]
      _ = MonoidHom.transfer (MonoidHom.transfer
            (χ₂.comp (MulEquiv.subgroupCongr hEq).toMonoidHom)) := by
            rw [transfer_subgroupCongr hEq χ₂]
      _ = MonoidHom.transfer ((χ₂.comp (MulEquiv.subgroupCongr hEq).toMonoidHom).comp
            (Subgroup.subgroupOfEquivOfLe inf_le_right).symm.toMonoidHom) :=
            transfer_transfer_eq _ (GammaHUpper M H ℓ) inf_le_right _
      _ = MonoidHom.transfer ((χ₂R.comp (MulEquiv.subgroupCongr hEq'.symm).toMonoidHom).comp
            (Subgroup.subgroupOfEquivOfLe inf_le_left).symm.toMonoidHom) := by rw [hS5]
      _ = MonoidHom.transfer (MonoidHom.transfer
            (χ₂R.comp (MulEquiv.subgroupCongr hEq'.symm).toMonoidHom)) :=
            (transfer_transfer_eq _ (iotaDeg M M' H H' d h).range inf_le_left _).symm
      _ = MonoidHom.transfer χ₂R.transfer := by
            rw [transfer_subgroupCongr hEq'.symm χ₂R]
      _ = MonoidHom.transfer (AddMonoidHom.toMultiplicativeRight
            (pushChar M M' H H' d A h (heckeT M' H' ℓ A φ))) := by rw [hS3]
  exact congrArg MonoidHom.toAdditiveLeft chain

#print axioms solution

end S_CohCarrier_jDeg_heckeT_comm_flat
end P2MW
export P2MW.S_CohCarrier_jDeg_heckeT_comm_flat (solution)
