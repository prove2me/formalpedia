-- Prove2me | solution 1 for CohCarrier.transfer_transitive
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/14ffac96-1b73-55bf-aeac-81edc105f9f0

import Mathlib.GroupTheory.Transfer
import Mathlib.GroupTheory.QuotientGroup.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_transfer_transitive

open Subgroup Subgroup.leftTransversals

namespace SolAux

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
  exact (MulAction.Quotient.mk_smul_out (H := L) g (g⁻¹ • p)).symm

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

end SolAux

open SolAux

theorem solution {G : Type*} [Group G] {C : Type*} [CommGroup C] (K L : Subgroup G) (hKL : K ≤ L)
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

#print axioms solution

end S_CohCarrier_transfer_transitive
end P2MW
export P2MW.S_CohCarrier_transfer_transitive (solution)
