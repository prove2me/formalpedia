-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormalODModule.nonempty_and_exists_isIsogenyOfHeight_and_exists_ringHom_centralizer_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/839236d3-6564-5adf-916f-943d6c90f0ba

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_nonempty_of_charP
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_isIsogenyOfHeight_of_isAlgClosed
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_ringHom_centralizer_injective_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormalODModule_nonempty_and_exists_isIsogenyOfHeight_and_exists_ringHom_centralizer_of_isAlgClosed
p2m_attr_erase "instance" "MvFormalGroup.CartierModule.instAddCommGroup MvFormalGroup.CartierModule.instNeg MvFormalGroup.CartierModule.instAdd MvFormalGroup.CartierModule.instZero MvFormalGroup.WittLaw.instTendstoCofiniteProdMk MvFormalGroup.CartierModule.instModuleWittVector instTopologicallyFGOfFiniteType MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup CerednikDrinfeld.LubinTate.instIsCommMap CerednikDrinfeld.LubinTate.instFintypeGaloisFieldTwo CerednikDrinfeld.LubinTate.sigma_isComm CerednikDrinfeld.LubinTate.sigmaBar_isComm CerednikDrinfeld.BoxBasisLemma.instDecidableInBox CerednikDrinfeld.Standard.law_isComm"
p2m_attr_erase "simp" "MvFormalGroup.CartierModule.toPowerSeries_sub MvFormalGroup.WittLaw.verFam_zero MvFormalGroup.WittLaw.verFam_succ MvFormalGroup.CartierModule.toPowerSeries_frobenius MvFormalGroup.CartierModule.toPowerSeries_verschiebung MvFormalGroup.WittLaw.blk_apply MvFormalGroup.WittLaw.weight_apply MvFormalGroup.CartierModule.toPowerSeries_map MvFormalGroup.CartierModule.toPowerSeries_precompFun MvFormalGroup.CartierModule.toPowerSeries_mapFun MvFormalGroup.CartierModule.mk.injEq MvFormalGroup.WittLaw.pairFam_apply MvFormalGroup.CartierModule.endAct_apply MvFormalGroup.WittLaw.frobFam_apply MvFormalGroup.CartierModule.toPowerSeries_zero MvFormalGroup.CartierModule.tangent_apply MvFormalGroup.CartierModule.toPowerSeries_precomp MvFormalGroup.CartierModule.Examples.toPowerSeries_addLinear MvFormalGroup.CartierModule.toPowerSeries_add MvFormalGroup.CartierModule.toPowerSeries_neg MvFormalGroup.CartierModule.mk.sizeOf_spec MvFormalGroup.CartierModule.inBlk_apply MvFormalGroup.WittLaw.teichFam_apply MvFormalGroup.CartierModule.toPowerSeries_homothety MvFormalGroup.WittLaw.verPoly_succ MvFormalGroup.WittLaw.xVec_coeff MvFormalGroup.WittLaw.cVec_coeff MvFormalGroup.WittLaw.cVec_mul MvFormalGroup.WittLaw.mulFam_apply MvFormalGroup.CartierModule.mapLinear_apply MvFormalGroup.WittLaw.cVec_add MvFormalGroup.WittLaw.cVec_zero MvFormalGroup.WittLaw.verPoly_zero MvFormalGroup.CartierModule.toPowerSeries_wittSMul MvFormalGroup.CartierModule.toPowerSeries_smul_witt MvFormalGroup.WittLaw.cVec_one MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt"
p2m_attr_erase "simp" "MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec CerednikDrinfeld.Standard.emb_inr CerednikDrinfeld.BoxBasisLemma.toFinsupp_apply CerednikDrinfeld.Standard.chi_zero CerednikDrinfeld.Standard.emb_inl CerednikDrinfeld.Standard.chi_one"

set_option autoImplicit false

universe u

theorem solution
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [IsAlgClosed k] [CharP k p]
    (j : CerednikDrinfeld.Zp2 p →+* k) :
    Nonempty (CerednikDrinfeld.SpecialFormalODModule p j) ∧
    (∀ Φ Φ' : CerednikDrinfeld.SpecialFormalODModule p j,
      ∃ (ρ : CerednikDrinfeld.SpecialFormal.Series k) (h : ℕ),
        CerednikDrinfeld.FormalODModule.IsIsogenyOfHeight Φ.toFormalODModule Φ'.toFormalODModule ρ h) ∧
    (∀ Φ : CerednikDrinfeld.SpecialFormalODModule p j,
      ∃ θ : Subring.centralizer
            (Set.range Φ.toFormalODModule.actEnd ∪ {Φ.toFormalODModule.varpiEnd}) →+*
          Matrix (Fin 2) (Fin 2) ℚ_[p],
        Function.Injective θ ∧
        ∃ m : ℕ,
          (∀ M : Matrix (Fin 2) (Fin 2) ℤ_[p],
            ∃ e, θ e = (p : ℚ_[p]) ^ m • M.map ((↑) : ℤ_[p] → ℚ_[p])) ∧
          (∀ e, ∃ M : Matrix (Fin 2) (Fin 2) ℤ_[p],
            (p : ℚ_[p]) ^ m • θ e = M.map ((↑) : ℤ_[p] → ℚ_[p]))) :=
  ⟨CerednikDrinfeld.SpecialFormalODModule.nonempty_of_charP p k j,
    CerednikDrinfeld.SpecialFormalODModule.exists_isIsogenyOfHeight_of_isAlgClosed p k j,
    CerednikDrinfeld.SpecialFormalODModule.exists_ringHom_centralizer_injective_of_isAlgClosed p k j⟩

end S_CerednikDrinfeld_SpecialFormalODModule_nonempty_and_exists_isIsogenyOfHeight_and_exists_ringHom_centralizer_of_isAlgClosed
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormalODModule_nonempty_and_exists_isIsogenyOfHeight_and_exists_ringHom_centralizer_of_isAlgClosed (solution)
