-- Prove2me | solution 1 for CohCarrier.jDeg_iDeg_cross_eq_index_smul_heckeT
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/f4cce190-d53d-58fc-bfdc-bf22cd0241cd

import Definitions.Def_CohCarrier_Level
import Mathlib.GroupTheory.QuotientGroup.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_jDeg_iDeg_cross_eq_index_smul_heckeT

set_option autoImplicit false
open scoped MatrixGroups
open Subgroup Subgroup.leftTransversals CohCarrier

namespace SolAux

variable {G : Type*} [Group G] {C : Type*} [CommGroup C]

theorem diff_one' {K : Subgroup G} [K.FiniteIndex] (S T : K.LeftTransversal) :
    diff (1 : K →* C) S T = 1 := by simp [diff]

theorem diff_mul' {K : Subgroup G} [K.FiniteIndex] (ϕ ψ : K →* C) (S T : K.LeftTransversal) :
    diff (ϕ * ψ) S T = diff ϕ S T * diff ψ S T := by
  simp only [diff, MonoidHom.mul_apply, Finset.prod_mul_distrib]

theorem transfer_one' {K : Subgroup G} [K.FiniteIndex] :
    MonoidHom.transfer (1 : K →* C) = 1 := by
  ext g; rw [MonoidHom.transfer_def _ default, diff_one']; rfl

theorem transfer_mul' {K : Subgroup G} [K.FiniteIndex] (ϕ ψ : K →* C) :
    MonoidHom.transfer (ϕ * ψ) = MonoidHom.transfer ϕ * MonoidHom.transfer ψ := by
  ext g
  rw [MonoidHom.mul_apply, MonoidHom.transfer_def _ default, MonoidHom.transfer_def _ default,
    MonoidHom.transfer_def _ default, diff_mul']

theorem transfer_pow' {K : Subgroup G} [K.FiniteIndex] (χ : K →* C) (n : ℕ) :
    MonoidHom.transfer (χ ^ n) = (MonoidHom.transfer χ) ^ n := by
  induction n with
  | zero => simp only [pow_zero, transfer_one']
  | succ n ih => simp only [pow_succ, transfer_mul', ih]

theorem transfer_restrict_eq_pow_index' (K : Subgroup G) [K.FiniteIndex] (φ : G →* C) :
    MonoidHom.transfer (φ.domRestrict K) = φ ^ K.index := by
  classical
  ext g
  letI := K.fintypeQuotientOfFiniteIndex
  rw [MonoidHom.transfer_def (φ.domRestrict K) default]
  show diff (φ.domRestrict K) default (g • default) = (φ g) ^ K.index
  unfold Subgroup.leftTransversals.diff
  simp only [MonoidHom.domRestrict_apply, map_mul, map_inv,
    Subgroup.smul_apply_eq_smul_apply_inv_smul, smul_eq_mul]
  rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, Finset.prod_mul_distrib,
    Finset.prod_const]
  have hreindex : (∏ q : G ⧸ K,
        φ ((default : K.LeftTransversal).2.leftQuotientEquiv (g⁻¹ • q) : G))
      = ∏ q : G ⧸ K, φ ((default : K.LeftTransversal).2.leftQuotientEquiv q : G) := by
    have := Equiv.prod_comp (MulAction.toPerm (g⁻¹ : G) : Equiv.Perm (G ⧸ K))
      (fun q => φ ((default : K.LeftTransversal).2.leftQuotientEquiv q : G))
    simpa only [MulAction.toPerm_apply] using this
  rw [hreindex, mul_comm ((φ g) ^ _) _, ← mul_assoc, inv_mul_cancel, one_mul,
    Subgroup.index_eq_card, Nat.card_eq_fintype_card, ← Finset.card_univ]

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

theorem transfer_transitive' (K L : Subgroup G) (hKL : K ≤ L)
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

end SolAux

open SolAux

namespace SolAux

variable {M M' d d' : ℕ} {H : Subgroup (ZMod M)ˣ} {H' : Subgroup (ZMod M')ˣ}
  {A : Type*} [AddCommGroup A]

theorem transfer_restrict_intermediate_impl {G : Type*} [Group G] {C : Type*} [CommGroup C]
    (K L : Subgroup G) (hKL : K ≤ L)
    [K.FiniteIndex] [L.FiniteIndex] [(K.subgroupOf L).FiniteIndex] (χ : L →* C) :
    MonoidHom.transfer ((χ.comp (Subgroup.inclusion hKL)) : K →* C)
      = (MonoidHom.transfer χ) ^ (K.subgroupOf L).index := by
  rw [transfer_transitive' K L hKL]
  have hrest : (χ.comp (Subgroup.inclusion hKL)).comp (Subgroup.subgroupOfEquivOfLe hKL).toMonoidHom
      = χ.domRestrict (K.subgroupOf L) := by
    ext k; rfl
  rw [hrest, transfer_restrict_eq_pow_index', transfer_pow']

theorem coresAdd_comp_inclusion_impl {G : Type*} [Group G] {B : Type*} [AddCommGroup B]
    (K L : Subgroup G) (hKL : K ≤ L)
    [K.FiniteIndex] [L.FiniteIndex] [(K.subgroupOf L).FiniteIndex] (χ : Additive ↥L →+ B) :
    coresAdd K (χ.comp (Subgroup.inclusion hKL).toAdditive)
      = (K.subgroupOf L).index • coresAdd L χ := by
  have key := transfer_restrict_intermediate_impl K L hKL (AddMonoidHom.toMultiplicativeRight χ)
  have hrest : (AddMonoidHom.toMultiplicativeRight χ).comp (Subgroup.inclusion hKL)
      = AddMonoidHom.toMultiplicativeRight (χ.comp (Subgroup.inclusion hKL).toAdditive) := by
    ext k; rfl
  rw [hrest] at key
  ext g
  simp only [coresAdd, key, AddMonoidHom.nsmul_apply,
    MonoidHom.toAdditiveLeft_apply_apply, MonoidHom.pow_apply,
    AddMonoidHom.toMultiplicativeRight_apply_apply, toAdd_pow, toAdd_ofAdd]

theorem conjUpperMat_conjLowerMat_impl (q d' : ℕ) [NeZero q] [NeZero d'] (γ : SL(2, ℤ))
    (hd : ((d' * q : ℕ) : ℤ) ∣ γ 1 0) :
    conjUpperMat q (conjLowerMat (d' * q) γ hd)
        (by show (q : ℤ) ∣ γ 0 1 * ((d' * q : ℕ) : ℤ); exact ⟨γ 0 1 * d', by push_cast; ring⟩)
      = conjLowerMat d' γ (dvd_trans (by push_cast; exact Dvd.intro q rfl) hd) := by
  have hq0 : (q : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hd'0 : (d' : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d')
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp only [conjUpperMat, conjLowerMat, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Fin.isValue]
  · rfl
  · push_cast; rw [← mul_assoc, Int.mul_ediv_cancel _ hq0]
  · obtain ⟨k, hk⟩ := hd; rw [hk]; push_cast
    rw [mul_comm ((d' : ℤ) * q) k, Int.mul_ediv_cancel _ (mul_ne_zero hd'0 hq0),
      mul_comm (d' : ℤ) q, ← mul_assoc, Int.mul_ediv_cancel _ hd'0]
  · rfl

theorem pushChar_iDeg'_cross_impl [NeZero d] [NeZero d'] (h : LevelLE M M' H H' d)
    (h' : LevelLE M M' H H' d') (φ : H1 M H A) (x : Additive ↥(iotaDeg M M' H H' d h).range) :
    pushChar M M' H H' d A h ((iDeg' M M' H H' d' A h') φ) x
      = φ (Additive.ofMul ((iotaDeg M M' H H' d' h')
          (((iotaDeg M M' H H' d h).ofInjective
            (iotaDeg_injective M M' H H' d h)).symm (Additive.toMul x)))) := rfl

theorem range_iotaDeg_le_GammaHUpper_impl (q : ℕ) [NeZero d] (h : LevelLE M M' H H' d)
    (hqd : (q : ℤ) ∣ (d : ℤ)) : (iotaDeg M M' H H' d h).range ≤ GammaHUpper M H q := by
  rintro k ⟨γ', rfl⟩
  show ((iotaDeg M M' H H' d h γ' : ↥(GammaH M H)) : SL(2, ℤ)) ∈ Gamma0Upper q
  show (((conjLowerMat d (γ' : SL(2, ℤ)) (h.dvd_entry γ')) : SL(2, ℤ)) 0 1 : ZMod q) = 0
  show (((γ' : SL(2, ℤ)) 0 1 * (d : ℤ) : ℤ) : ZMod q) = 0
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact dvd_mul_of_dvd_right hqd _

theorem pushChar_iDeg'_eq_conjL_inclusion_impl (q : ℕ) [NeZero d] [NeZero d'] [NeZero q]
    (h : LevelLE M M' H H' d) (h' : LevelLE M M' H H' d')
    (hqd : (q : ℤ) ∣ (d : ℤ)) (hdiv : d = d' * q) (φ : H1 M H A) :
    pushChar M M' H H' d A h ((iDeg' M M' H H' d' A h') φ)
      = (φ.comp (conjL M H q).toAdditive).comp
          (Subgroup.inclusion (range_iotaDeg_le_GammaHUpper_impl q h hqd)).toAdditive := by
  subst hdiv
  refine AddMonoidHom.ext fun x => ?_
  rw [pushChar_iDeg'_cross_impl h h' φ x]
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, MonoidHom.toAdditive_apply_apply]
  set γ' := (MonoidHom.ofInjective (iotaDeg_injective M M' H H' (d' * q) h)).symm
    (Additive.toMul x) with hγ'
  have hk : (iotaDeg M M' H H' (d' * q) h) γ' = ↑(Additive.toMul x) :=
    MonoidHom.apply_ofInjective_symm (iotaDeg_injective M M' H H' (d' * q) h) (Additive.toMul x)
  refine congrArg (φ ∘ Additive.ofMul) (Subtype.ext ?_)
  show (conjLowerMat d' (γ' : SL(2, ℤ)) (h'.dvd_entry γ') : SL(2, ℤ))
    = (conjUpperMat q ((↑(Additive.toMul x) : ↥(GammaH M H)) : SL(2, ℤ))
        (dvd_of_mem_GammaHUpper M H q
          (Subgroup.inclusion (range_iotaDeg_le_GammaHUpper_impl q h hqd)
            (Additive.toMul x))) : SL(2, ℤ))
  simp only [← hk]
  exact (conjUpperMat_conjLowerMat_impl q d' (γ' : SL(2, ℤ)) (h.dvd_entry γ')).symm

end SolAux

open SolAux

theorem solution {M M' d d' : ℕ} {H : Subgroup (ZMod M)ˣ} {H' : Subgroup (ZMod M')ˣ}
    {A : Type*} [AddCommGroup A] (q : ℕ) [NeZero M'] [NeZero d] [NeZero d'] [NeZero q]
    (h : LevelLE M M' H H' d) (h' : LevelLE M M' H H' d')
    (hqd : (q : ℤ) ∣ (d : ℤ)) (hdiv : d = d' * q) (φ : H1 M H A) :
    (jDeg M M' H H' d A h) ((iDeg' M M' H H' d' A h') φ)
      = (((iotaDeg M M' H H' d h).range).subgroupOf (GammaHUpper M H q)).index
          • heckeT M H q A φ := by
  show coresAdd _ (pushChar M M' H H' d A h ((iDeg' M M' H H' d' A h') φ)) = _
  rw [pushChar_iDeg'_eq_conjL_inclusion_impl q h h' hqd hdiv φ,
    coresAdd_comp_inclusion_impl _ _ (range_iotaDeg_le_GammaHUpper_impl q h hqd)]
  rfl

#print axioms solution

end S_CohCarrier_jDeg_iDeg_cross_eq_index_smul_heckeT
end P2MW
export P2MW.S_CohCarrier_jDeg_iDeg_cross_eq_index_smul_heckeT (solution)
