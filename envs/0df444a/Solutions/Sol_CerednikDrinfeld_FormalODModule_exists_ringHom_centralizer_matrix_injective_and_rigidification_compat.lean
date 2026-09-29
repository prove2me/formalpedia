-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_ringHom_centralizer_matrix_injective_and_rigidification_compat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/09d10b4c-d264-5d3b-909e-d9a87cac4392

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Definitions.Def_CerednikDrinfeld_PeriodMap
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_ringHom_centralizer_matrix_smul_eq_map_and_nsmul_apply_rigidification_eq
import Theorems.Thm_CerednikDrinfeld_FormalODModule_injective_and_exists_pow_smul_map_eq_of_ringHom_centralizer_rigidification_compat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_ringHom_centralizer_matrix_injective_and_rigidification_compat
p2m_attr_erase "instance" "MvFormalGroup.CartierModule.instModulePadicInt MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup instTopologicallyFGOfFiniteType CerednikDrinfeld.LubinTate.instIsCommMap CerednikDrinfeld.LubinTate.instFintypeGaloisFieldTwo CerednikDrinfeld.LubinTate.sigma_isComm CerednikDrinfeld.LubinTate.sigmaBar_isComm CerednikDrinfeld.BoxBasisLemma.instDecidableInBox CerednikDrinfeld.Standard.law_isComm"
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt CerednikDrinfeld.Standard.emb_inr CerednikDrinfeld.BoxBasisLemma.toFinsupp_apply CerednikDrinfeld.Standard.chi_zero CerednikDrinfeld.Standard.emb_inl CerednikDrinfeld.Standard.chi_one"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

namespace ReduceETR

theorem map_coe_injective {p : ℕ} [Fact p.Prime] :
    Function.Injective (fun A : Matrix (Fin 2) (Fin 2) ℤ_[p] => A.map ((↑) : ℤ_[p] → ℚ_[p])) :=
  fun A B h => Matrix.ext fun i j => PadicInt.ext (by simpa using congrFun (congrFun h i) j)

theorem map_coe_smul {p : ℕ} [Fact p.Prime] (c : ℤ_[p]) (A : Matrix (Fin 2) (Fin 2) ℤ_[p]) :
    (c • A).map ((↑) : ℤ_[p] → ℚ_[p]) = (c : ℚ_[p]) • A.map ((↑) : ℤ_[p] → ℚ_[p]) := by
  ext i j; simp

end ReduceETR

theorem solution
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι)) (hΦ4 : Φ.HasHeight 4)
    (hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0) (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
    (hrΦ : ∀ (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
      (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L),
      Set.BijOn rΦ Set.univ ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung 0 : Set _)) :
    ∃ (E : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) ℚ_[p]) (m : ℕ),
      Function.Injective E ∧
      (∀ A : Matrix (Fin 2) (Fin 2) ℤ_[p], ∃ e, E e = (p : ℚ_[p]) ^ m • A.map ((↑) : ℤ_[p] → ℚ_[p])) ∧
      (∀ e, ∃ A : Matrix (Fin 2) (Fin 2) ℤ_[p], (p : ℚ_[p]) ^ m • E e = A.map ((↑) : ℤ_[p] → ℚ_[p])) ∧
      (∀ (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (A : Matrix (Fin 2) (Fin 2) ℤ_[p]),
        (p : ℚ_[p]) ^ m • E e = A.map ((↑) : ℤ_[p] → ℚ_[p]) →
        ∀ (Ne : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod),
          (∀ x : MvFormalGroup.CartierModule p Φ.F × (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).Sigma,
            Ne ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk x) =
              (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk
                (MvFormalGroup.CartierModule.endAct (e : MvFormalGroup.End Φ.F) x.1,
                 (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).toSigma
                   (MvFormalGroup.CartierModule.endAct (e : MvFormalGroup.End Φ.F)
                     ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).ofSigma x.2)))) →
          ∀ w : Fin 2 → ℤ_[p], p ^ m • Ne (rΦ w) = rΦ (A.mulVec w)) := by
  obtain ⟨E, hNe, hE⟩ :=
    CerednikDrinfeld.FormalODModule.exists_ringHom_centralizer_matrix_smul_eq_map_and_nsmul_apply_rigidification_eq p k ι Φ hΦ hΦ4 hcΦ rΦ hrΦ
  obtain ⟨hinj, m, hfull⟩ :=
    CerednikDrinfeld.FormalODModule.injective_and_exists_pow_smul_map_eq_of_ringHom_centralizer_rigidification_compat p k ι Φ hΦ hΦ4 hcΦ rΦ hrΦ E hNe hE
  refine ⟨E, m + 1, hinj, ?_, ?_, ?_⟩
  ·
    intro A
    obtain ⟨e, he⟩ := hfull ((p : ℤ_[p]) • A)
    refine ⟨e, ?_⟩
    rw [he, ReduceETR.map_coe_smul, smul_smul, pow_succ]
    norm_cast
  ·
    intro e
    obtain ⟨A, hA, -⟩ := hE e
    refine ⟨(p : ℤ_[p]) ^ m • A, ?_⟩
    rw [ReduceETR.map_coe_smul, ← hA, smul_smul, pow_succ]
    norm_cast
  ·
    intro e A' hA' Ne hNe' w
    obtain ⟨A, hA, hcomp⟩ := hE e
    have hAA' : A' = (p : ℤ_[p]) ^ m • A := by
      apply ReduceETR.map_coe_injective
      show A'.map _ = ((p : ℤ_[p]) ^ m • A).map _
      rw [← hA', ReduceETR.map_coe_smul, ← hA, smul_smul, pow_succ]
      norm_cast
    have h1 := hcomp Ne hNe' w
    rw [hAA', Matrix.smul_mulVec, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, map_nsmul, ← h1, smul_smul,
      pow_succ]

#print axioms solution

end S_CerednikDrinfeld_FormalODModule_exists_ringHom_centralizer_matrix_injective_and_rigidification_compat
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_ringHom_centralizer_matrix_injective_and_rigidification_compat (solution)
