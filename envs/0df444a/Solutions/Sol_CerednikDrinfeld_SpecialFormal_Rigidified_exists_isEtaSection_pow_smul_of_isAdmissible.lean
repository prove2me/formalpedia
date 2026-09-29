-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.exists_isEtaSection_pow_smul_of_isAdmissible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/8787bf77-ac52-52e3-a04e-12da0e5ea2f3

import Mathlib
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_lambda_injective_of_isHomogeneousVBasis_of_torsionFree
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_nsmul_rigidNum_mem_eta
import Theorems.Thm_CerednikDrinfeld_FormalODModule_nMap_bijOn_eta_of_eq_baseChangeEq_mk
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_isCompl_nPiece_zero_one
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_IsCanonicalLMap_exists_mem_etaPiece_add_eq
import Theorems.Thm_CerednikDrinfeld_FormalODModule_IsODHom_map_mem_gradedPiece
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_IsCanonicalLMap_comp_eq_nMap_comp_of_isNilpotent
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isCanonicalLMap_toGradedCartierModuleData
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isCompl_gradedPiece_zero_one_of_isNilpotent
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isBaseChangeAlong_toGradedCartierModuleData_baseChange
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isHomogeneousVBasis_of_isHomogeneousVBasis_toGradedCartierModuleData
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isSpecialCartierModule_toGradedCartierModuleData
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isEtaSection_pow_smul_of_isAdmissible
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt"

set_option autoImplicit false

p2m_open "CerednikDrinfeld P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isEtaSection_pow_smul_of_isAdmissible.CerednikDrinfeld CerednikDrinfeld.SpecialFormal P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isEtaSection_pow_smul_of_isAdmissible.CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega"

open scoped PadicInt Padic

p2m_open "MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isEtaSection_pow_smul_of_isAdmissible.CerednikDrinfeld CerednikDrinfeld.GradedCartierModuleData P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isEtaSection_pow_smul_of_isAdmissible.CerednikDrinfeld.GradedCartierModuleData CerednikDrinfeld.SpecialFormal P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isEtaSection_pow_smul_of_isAdmissible.CerednikDrinfeld.SpecialFormal CerednikDrinfeld.SpecialFormal.Rigidified P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isEtaSection_pow_smul_of_isAdmissible.CerednikDrinfeld.SpecialFormal.Rigidified"

namespace W1Aux

variable {p : ℕ} [Fact p.Prime]

theorem isBaseChangeAlong'_of_eq {B S : Type} [CommRing B] [CommRing S] (j : Zp2 p →+* B)
    (g : B →+* S) (X : FormalODModule p B)
    (γ : Fin 2 → CartierModule p X.F) (hγ : X.IsHomogeneousVBasis j γ)
    (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))
    (X' : FormalODModule p S) (hX : X.map g = X') (j' : Zp2 p →+* S) (hj : g.comp j = j')
    (hc' : IsCompl (X'.gradedPiece j' 0) (X'.gradedPiece j' 1))
    (hF : X.F.map g = X'.F) :
    IsBaseChangeAlong' g (X.toGradedCartierModuleData j hc) (X'.toGradedCartierModuleData j' hc')
      (CartierModule.baseChangeEq g hF) := by
  subst hX; subst hj
  exact CerednikDrinfeld.FormalODModule.isBaseChangeAlong_toGradedCartierModuleData_baseChange p j g X γ hγ hc hc'

theorem natL_of_eq {B B' : Type} [CommRing B] [CommRing B'] (j : Zp2 p →+* B) (φ : B →+* B')
    (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B'))
    (D : GradedCartierModuleData p B j) (hD : D.IsSpecialCartierModule)
    (j' : Zp2 p →+* B') (hj : φ.comp j = j')
    (D' : GradedCartierModuleData p B' j') (hD' : D'.IsSpecialCartierModule)
    (f : D.M →+ D'.M) (hf : IsBaseChangeAlong' φ D D' f)
    (L : D.M →+ D.NMod) (hL : D.IsCanonicalLMap L)
    (L' : D'.M →+ D'.NMod) (hL' : D'.IsCanonicalLMap L') :
    ∀ x : D.M, L' (f x) = D.nMap D' f hf.2.2.1 hf.2.2.2.1 (L x) := by
  subst hj
  exact CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.comp_eq_nMap_comp_of_isNilpotent p j φ hB hB' D hD D' hD' f hf L hL L' hL'

theorem redBij_of_eq {S : Type} [CommRing S] (hS : IsNilpotent (p : S))
    (j : Zp2 p →+* S) (X : FormalODModule p S)
    (γ : Fin 2 → CartierModule p X.F) (hγ : X.IsHomogeneousVBasis j γ)
    (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))
    (Xb : FormalODModule p (S ⧸ pIdeal p S)) (hXb : X.map (Ideal.Quotient.mk (pIdeal p S)) = Xb)
    (jb : Zp2 p →+* S ⧸ pIdeal p S) (hjb : (Ideal.Quotient.mk (pIdeal p S)).comp j = jb)
    (hcb : IsCompl (Xb.gradedPiece jb 0) (Xb.gradedPiece jb 1))
    (hF : X.F.map (Ideal.Quotient.mk (pIdeal p S)) = Xb.F)
    (red : CartierModule p X.F →+ CartierModule p Xb.F)
    (hred : red = CartierModule.baseChangeEq (Ideal.Quotient.mk (pIdeal p S)) hF)
    (hredV : ∀ x, red ((X.toGradedCartierModuleData j hc).verschiebung x) =
      (Xb.toGradedCartierModuleData jb hcb).verschiebung (red x))
    (hredPi : ∀ x, red ((X.toGradedCartierModuleData j hc).varpi x) =
      (Xb.toGradedCartierModuleData jb hcb).varpi (red x))
    (L : _) (hL : (X.toGradedCartierModuleData j hc).IsCanonicalLMap L)
    (Lb : _) (hLb : (Xb.toGradedCartierModuleData jb hcb).IsCanonicalLMap Lb)
    (hLL : ∀ x, Lb (red x) = (X.toGradedCartierModuleData j hc).nMap (Xb.toGradedCartierModuleData jb hcb) red hredV hredPi (L x)) :
    Set.BijOn ((X.toGradedCartierModuleData j hc).nMap (Xb.toGradedCartierModuleData jb hcb) red hredV hredPi)
      ((X.toGradedCartierModuleData j hc).eta L hL.isCartierLMap.map_verschiebung : Set _)
      ((Xb.toGradedCartierModuleData jb hcb).eta Lb hLb.isCartierLMap.map_verschiebung : Set _) :=
  CerednikDrinfeld.FormalODModule.nMap_bijOn_eta_of_eq_baseChangeEq_mk p hS j X γ hγ hc Xb hXb jb hjb hcb hF red hred
    hredV hredPi L hL Lb hLb hLL

theorem isHausdorff_of_isNilpotent {S : Type} [CommRing S] (hS : IsNilpotent ((p : ℕ) : S)) :
    IsHausdorff (Ideal.span {((p : ℕ) : S)}) S := by
  obtain ⟨N, hN⟩ := hS
  refine ⟨fun x hx => ?_⟩
  have := hx N
  rwa [Ideal.span_singleton_pow, hN, Ideal.span_singleton_eq_bot.mpr rfl, Submodule.bot_smul, SModEq.bot] at this

theorem nMap_mem_nPiece {B B' : Type} [CommRing B] [CommRing B'] {j : Zp2 p →+* B} {j' : Zp2 p →+* B'}
    (D : GradedCartierModuleData p B j) (D' : GradedCartierModuleData p B' j') (f : D.M →+ D'.M)
    (hV : ∀ x, f (D.verschiebung x) = D'.verschiebung (f x))
    (hPi : ∀ x, f (D.varpi x) = D'.varpi (f x))
    (hpc : ∀ (i : Fin 2) (x : D.M), x ∈ D.piece i → f x ∈ D'.piece i)
    (m : Fin 2) (n : D.NMod) (hn : n ∈ D.nPiece m) : D.nMap D' f hV hPi n ∈ D'.nPiece m := by
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := AddSubgroup.mem_map.mp hn
  obtain ⟨ha, hb⟩ := AddSubgroup.mem_prod.mp hab
  rw [nMap_nMk]
  exact AddSubgroup.mem_map.mpr ⟨(f a, f b), AddSubgroup.mem_prod.mpr ⟨hpc m a ha, hpc m b hb⟩, rfl⟩

end W1Aux

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "Zp2 FormalODModule FormalODModule.map_map FormalODModule.IsODHom SpecialFormal.Rigidified GradedCartierModuleData GradedCartierModuleData.IsCanonicalLMap SpecialFormal.Rigidified.nsmul_rigidNum_mem_eta FormalODModule.mem_toGradedCartierModuleData_piece_iff FormalODModule.baseChange_mem_gradedPiece FormalODModule.nMap_bijOn_eta_of_eq_baseChangeEq_mk GradedCartierModuleData.isCompl_nPiece_zero_one GradedCartierModuleData.IsCanonicalLMap.exists_mem_etaPiece_add_eq FormalODModule.IsODHom.map_mem_gradedPiece GradedCartierModuleData.IsCanonicalLMap.comp_eq_nMap_comp_of_isNilpotent FormalODModule.exists_isCanonicalLMap_toGradedCartierModuleData FormalODModule.isBaseChangeAlong_toGradedCartierModuleData_baseChange FormalODModule.isHomogeneousVBasis_of_isHomogeneousVBasis_toGradedCartierModuleData FormalODModule.isSpecialCartierModule_toGradedCartierModuleData"
namespace GradedCartierModuleData
p2m_export "CerednikDrinfeld.GradedCartierModuleData" "lambda_injective_of_isHomogeneousVBasis_of_torsionFree IsHomogeneousVBasis IsSpecialCartierModule varpi_varpi varpi module mk M piece verschiebung varpi_mem varpi_verschiebung varpi_frobenius NMod nMk nMk_surjective lambda lambda_nMk nVarpi nPiece nMap nMap_nMk IsBaseChangeAlong' IsCartierLMap IsCanonicalLMap phi phi_nMk eta mem_eta_iff etaPiece u isCompl_nPiece_zero_one IsCanonicalLMap.exists_mem_etaPiece_add_eq IsCanonicalLMap.comp_eq_nMap_comp_of_isNilpotent"
p2m_open "CerednikDrinfeld.GradedCartierModuleData CerednikDrinfeld"

variable {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] {j : Zp2 p →+* B}
variable (D : GradedCartierModuleData p B j)

private theorem _root_.CerednikDrinfeld.GradedCartierModuleData.QXA_nVarpi_nMk (m m' : D.M) : D.nVarpi (D.nMk (m, m')) = D.nMk (D.varpi m, D.varpi m') := rfl

p2m_export "CerednikDrinfeld.GradedCartierModuleData" "QXA_nVarpi_nMk"
private theorem _root_.CerednikDrinfeld.GradedCartierModuleData.QXA_nVarpi_nVarpi (z : D.NMod) : D.nVarpi (D.nVarpi z) = (p : ℕ) • z := by
  obtain ⟨⟨m, m'⟩, rfl⟩ := D.nMk_surjective z
  rw [QXA_nVarpi_nMk, QXA_nVarpi_nMk, D.varpi_varpi, D.varpi_varpi, ← map_nsmul]
  rfl

p2m_export "CerednikDrinfeld.GradedCartierModuleData" "QXA_nVarpi_nVarpi"
private theorem _root_.CerednikDrinfeld.GradedCartierModuleData.QXA_nVarpi_mem_nPiece {i : Fin 2} {z : D.NMod} (hz : z ∈ D.nPiece i) :
    D.nVarpi z ∈ D.nPiece (i + 1) := by
  obtain ⟨⟨m, m'⟩, hmm, rfl⟩ := hz
  exact ⟨(D.varpi m, D.varpi m'), ⟨D.varpi_mem i m hmm.1, D.varpi_mem i m' hmm.2⟩,
    (D.QXA_nVarpi_nMk m m').symm⟩

p2m_export "CerednikDrinfeld.GradedCartierModuleData" "QXA_nVarpi_mem_nPiece"
theorem QXA_lambda_nVarpi (z : D.NMod) : D.lambda (D.nVarpi z) = D.varpi (D.lambda z) := by
  obtain ⟨⟨m, m'⟩, rfl⟩ := D.nMk_surjective z
  rw [QXA_nVarpi_nMk, lambda_nMk, lambda_nMk, map_add, D.varpi_verschiebung]

private theorem _root_.CerednikDrinfeld.GradedCartierModuleData.QXA_nMap_nVarpi {B' : Type} [CommRing B'] {j' : Zp2 p →+* B'} (D' : GradedCartierModuleData p B' j')
    (f : D.M →+ D'.M) (hV : ∀ x, f (D.verschiebung x) = D'.verschiebung (f x))
    (hPi : ∀ x, f (D.varpi x) = D'.varpi (f x)) (z : D.NMod) :
    D.nMap D' f hV hPi (D.nVarpi z) = D'.nVarpi (D.nMap D' f hV hPi z) := by
  obtain ⟨⟨m, m'⟩, rfl⟩ := D.nMk_surjective z
  rw [QXA_nVarpi_nMk, nMap_nMk, nMap_nMk, QXA_nVarpi_nMk, hPi, hPi]

p2m_export "CerednikDrinfeld.GradedCartierModuleData" "QXA_nMap_nVarpi"

private theorem _root_.CerednikDrinfeld.GradedCartierModuleData.QXA_IsCartierLMap_map_varpi (hB : ∀ b : B, (p : B) * b = 0 → b = 0)
    (γ : Fin 2 → D.M) (hγ : D.IsHomogeneousVBasis γ) {L : D.M →+ D.NMod} (hL : D.IsCartierLMap L)
    (x : D.M) : L (D.varpi x) = D.nVarpi (L x) := by
  apply lambda_injective_of_isHomogeneousVBasis_of_torsionFree p j hB D γ hγ
  rw [hL.lambda_comp, QXA_lambda_nVarpi, hL.lambda_comp, D.varpi_frobenius]

p2m_export "CerednikDrinfeld.GradedCartierModuleData" "QXA_IsCartierLMap_map_varpi"

private theorem _root_.CerednikDrinfeld.GradedCartierModuleData.QXA_IsCanonicalLMap_map_varpi {L : D.M →+ D.NMod} (hL : D.IsCanonicalLMap L) (x : D.M) :
    L (D.varpi x) = D.nVarpi (L x) := by
  obtain ⟨S, _, jS, φ, hφ, htf, Dl, hDl, f, hf, Ll, hLl, hcomp⟩ := hL.exists_lift
  obtain ⟨γ, hγl, hγ⟩ := hf.2.2.2.2.2
  have hfγ : ∀ i, L (D.varpi (f (γ i))) = D.nVarpi (L (f (γ i))) := by
    intro i
    rw [← hf.2.2.2.1, hcomp, hcomp, Dl.QXA_IsCartierLMap_map_varpi htf γ hγl hLl,
      Dl.QXA_nMap_nVarpi]
  obtain ⟨⟨c, y⟩, hx, -⟩ := hγ.2 x
  subst hx
  simp only [map_add, map_sum, LinearMap.map_smul]
  rw [D.varpi_verschiebung, hL.isCartierLMap.map_verschiebung, hL.isCartierLMap.map_verschiebung,
    QXA_nVarpi_nMk, map_zero]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hL.isCartierLMap.map_smul, hL.isCartierLMap.map_smul, hfγ i, LinearMap.map_smul]

p2m_export "CerednikDrinfeld.GradedCartierModuleData" "QXA_IsCanonicalLMap_map_varpi"
private theorem _root_.CerednikDrinfeld.GradedCartierModuleData.QXA_phi_nVarpi {L : D.M →+ D.NMod} (hL : D.IsCanonicalLMap L) (z : D.NMod) :
    D.phi L hL.isCartierLMap.map_verschiebung (D.nVarpi z) =
      D.nVarpi (D.phi L hL.isCartierLMap.map_verschiebung z) := by
  obtain ⟨⟨m, m'⟩, rfl⟩ := D.nMk_surjective z
  rw [QXA_nVarpi_nMk, phi_nMk, phi_nMk, map_add, D.QXA_IsCanonicalLMap_map_varpi hL,
    QXA_nVarpi_nMk, map_zero]

p2m_export "CerednikDrinfeld.GradedCartierModuleData" "QXA_phi_nVarpi"
private theorem _root_.CerednikDrinfeld.GradedCartierModuleData.QXA_nVarpi_mem_etaPiece {L : D.M →+ D.NMod} (hL : D.IsCanonicalLMap L) {i : Fin 2}
    {z : D.NMod} (hz : z ∈ D.etaPiece L hL.isCartierLMap.map_verschiebung i) :
    D.nVarpi z ∈ D.etaPiece L hL.isCartierLMap.map_verschiebung (i + 1) := by
  refine AddSubgroup.mem_inf.2 ⟨?_, D.QXA_nVarpi_mem_nPiece (AddSubgroup.mem_inf.1 hz).2⟩
  rw [mem_eta_iff, D.QXA_phi_nVarpi hL, (D.mem_eta_iff _ _ _).1 (AddSubgroup.mem_inf.1 hz).1]

p2m_export "CerednikDrinfeld.GradedCartierModuleData" "QXA_nVarpi_mem_etaPiece"
end CerednikDrinfeld.GradedCartierModuleData

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "Zp2 FormalODModule FormalODModule.map_map FormalODModule.IsODHom SpecialFormal.Rigidified GradedCartierModuleData GradedCartierModuleData.IsCanonicalLMap SpecialFormal.Rigidified.nsmul_rigidNum_mem_eta FormalODModule.mem_toGradedCartierModuleData_piece_iff FormalODModule.baseChange_mem_gradedPiece FormalODModule.nMap_bijOn_eta_of_eq_baseChangeEq_mk GradedCartierModuleData.isCompl_nPiece_zero_one GradedCartierModuleData.IsCanonicalLMap.exists_mem_etaPiece_add_eq FormalODModule.IsODHom.map_mem_gradedPiece GradedCartierModuleData.IsCanonicalLMap.comp_eq_nMap_comp_of_isNilpotent FormalODModule.exists_isCanonicalLMap_toGradedCartierModuleData FormalODModule.isBaseChangeAlong_toGradedCartierModuleData_baseChange FormalODModule.isHomogeneousVBasis_of_isHomogeneousVBasis_toGradedCartierModuleData FormalODModule.isSpecialCartierModule_toGradedCartierModuleData"
namespace SpecialFormal
p2m_export "CerednikDrinfeld.SpecialFormal" "pIdeal residueMap reduceMap structureMap Rigidified Rigidified.nsmul_rigidNum_mem_eta Rigidified.jbar Rigidified.PhibarS Rigidified.bcPhi Rigidified.rhoC Rigidified.bcPhi_verschiebungInt Rigidified.bcPhi_endAct_varpiEnd Rigidified.rhoC_verschiebungInt Rigidified.rhoC_endAct_varpiEnd Rigidified.jS Rigidified.jSbar Rigidified.jPhiS Rigidified.IsGradedPhiS Rigidified.rigidNum Rigidified.isEtaSection_zero_iff Rigidified.isEtaSection_one_iff"
namespace Rigidified
p2m_export "CerednikDrinfeld.SpecialFormal.Rigidified" "Xbar Φbar IsAdmissible map mk n ρ X nsmul_rigidNum_mem_eta jbar XS XbarS PhibarS XS_F_map_mk redC bcPhi rhoC redC_verschiebungInt redC_endAct_varpiEnd bcPhi_verschiebungInt bcPhi_endAct_varpiEnd rhoC_verschiebungInt rhoC_endAct_varpiEnd jS jSbar jPhiS IsGradedS IsGradedSbar IsGradedPhiS etaRed rigidNum LatticeRel IsEtaSection isEtaSection_zero_iff isEtaSection_one_iff"
p2m_open "CerednikDrinfeld.SpecialFormal.Rigidified CerednikDrinfeld.SpecialFormal CerednikDrinfeld"

theorem QXA_LatticeRel_smul {p : ℕ} [Fact p.Prime] {S' : Type} [CommRing S'] {jS' : Zp2 p →+* S'}
    {E : GradedCartierModuleData p S' jS'} {n : ℕ} {r : (Fin 2 → ℤ_[p]) →+ E.NMod} {zbar : E.NMod}
    {v : Fin 2 → ℚ_[p]} (h : LatticeRel E n r zbar v) :
    LatticeRel E n r ((p : ℕ) • zbar) ((p : ℚ_[p]) • v) := by
  obtain ⟨m, k, w, hv, hr⟩ := h
  refine ⟨m, k, (p : ℕ) • w, ?_, ?_⟩
  · rw [smul_comm, hv]
    funext i
    simp only [Pi.smul_apply, nsmul_eq_mul, PadicInt.coe_mul, PadicInt.coe_natCast, smul_eq_mul]
  · rw [map_nsmul, smul_smul, mul_comm, ← smul_smul, hr, smul_smul, smul_smul, mul_comm]

end CerednikDrinfeld.SpecialFormal.Rigidified

open W1Aux

theorem W1_core
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    (Φ : FormalODModule p (O ⧸ pIdeal p O))
    (hcΦ : IsCompl (Φ.gradedPiece (Rigidified.jbar ι) 0) (Φ.gradedPiece (Rigidified.jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
    (hLΦ : ∃ L : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).M →+
        (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod,
      (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).IsCanonicalLMap L)
    (hrΦ : ∀ (L : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).M →+
        (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
      (hL : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).IsCanonicalLMap L),
      Set.BijOn rΦ Set.univ
        ((Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).etaPiece L
          hL.isCartierLMap.map_verschiebung 0 : Set _))
    {B : Type} [CommRing B] (ψ : O →+* B)
    (t : Rigidified p Φ B) (hOD : FormalODModule.IsODHom (t.Φbar ψ) t.Xbar t.ρ)
    {S : Type} [CommRing S] [Algebra ℤ_[p] S] (g : B →+* S) (hS : IsNilpotent (p : S))
    (hc : t.IsGradedS ι ψ g) (hcb : t.IsGradedSbar ι ψ g) (hcΦg : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ g)
    (L : _) (hL : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).IsCanonicalLMap L)
    (w : Fin 2 → ℤ_[p]) :
    ∃ z ∈ ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).etaPiece L hL.isCartierLMap.map_verschiebung 0,
      t.etaRed ι ψ g hc hcb z = p • Rigidified.rigidNum ι hcΦ rΦ ψ t hOD g hcb hcΦg w := by
  classical

  have hp0 : IsNilpotent ((p : ℕ) : S ⧸ pIdeal p S) :=
    ⟨1, by rw [pow_one]; exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))⟩

  have hmk : (Ideal.Quotient.mk (pIdeal p S)).comp g = (reduceMap (p := p) g).comp (Ideal.Quotient.mk (pIdeal p B)) := by
    ext b; rfl
  have hXm : (t.XS g).map (Ideal.Quotient.mk (pIdeal p S)) = t.XbarS g := by
    show (t.X.map g).map (Ideal.Quotient.mk (pIdeal p S)) = (t.X.map (Ideal.Quotient.mk (pIdeal p B))).map (reduceMap (p := p) g)
    rw [FormalODModule.map_map, FormalODModule.map_map, hmk]
  have hjb : (Ideal.Quotient.mk (pIdeal p S)).comp (Rigidified.jS ι ψ g) = Rigidified.jSbar ι ψ g := by
    show (Ideal.Quotient.mk (pIdeal p S)).comp (g.comp (structureMap ι ψ)) = (reduceMap (p := p) g).comp ((Ideal.Quotient.mk (pIdeal p B)).comp (structureMap ι ψ))
    rw [← RingHom.comp_assoc, hmk, RingHom.comp_assoc]
  have hF : (t.XS g).F.map (Ideal.Quotient.mk (pIdeal p S)) = (t.XbarS g).F := t.XS_F_map_mk g

  obtain ⟨Sl, _, jl, φl, _, _, Dl, _, fl, hfl, Ll, _, _⟩ := hL.exists_lift
  obtain ⟨γl, _, hγf⟩ := hfl.2.2.2.2.2
  have hγ : (t.XS g).IsHomogeneousVBasis (Rigidified.jS ι ψ g) (fun i => fl (γl i)) :=
    CerednikDrinfeld.FormalODModule.isHomogeneousVBasis_of_isHomogeneousVBasis_toGradedCartierModuleData p _ _ hc _ hγf

  have hbca : IsBaseChangeAlong' (Ideal.Quotient.mk (pIdeal p S)) ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc) ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb) (CartierModule.baseChangeEq (Ideal.Quotient.mk (pIdeal p S)) hF) :=
    isBaseChangeAlong'_of_eq _ _ _ _ hγ hc _ hXm _ hjb hcb hF
  have hγb : (t.XbarS g).IsHomogeneousVBasis (Rigidified.jSbar ι ψ g)
      (fun i => CartierModule.baseChangeEq (Ideal.Quotient.mk (pIdeal p S)) hF (fl (γl i))) := by
    refine ⟨fun i => ?_, isUnit_det_tangent_baseChangeEq _ hF _ hγ.2⟩
    exact (FormalODModule.mem_toGradedCartierModuleData_piece_iff _ _ hcb i _).mp
      (hbca.2.2.2.2.1 i _ ((FormalODModule.mem_toGradedCartierModuleData_piece_iff _ _ hc i _).mpr (hγ.1 i)))
  obtain ⟨Lb, hLb⟩ := CerednikDrinfeld.FormalODModule.exists_isCanonicalLMap_toGradedCartierModuleData p
    (Rigidified.jSbar ι ψ g) (isHausdorff_of_isNilpotent hp0) _ _ hγb hcb
  have hD : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).IsSpecialCartierModule :=
    (CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData p _ _ _ hγ hc).2
  have hDb : ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).IsSpecialCartierModule :=
    (CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData p _ _ _ hγb hcb).2

  have hLLb : ∀ x, Lb (CartierModule.baseChangeEq (Ideal.Quotient.mk (pIdeal p S)) hF x) =
      ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nMap ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb) (CartierModule.baseChangeEq (Ideal.Quotient.mk (pIdeal p S)) hF) hbca.2.2.1 hbca.2.2.2.1 (L x) :=
    natL_of_eq _ (Ideal.Quotient.mk (pIdeal p S)) hS hp0 ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc) hD _ hjb ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb) hDb _ hbca L hL Lb hLb

  have hbij := redBij_of_eq hS (Rigidified.jS ι ψ g) (t.XS g) _ hγ hc (t.XbarS g) hXm (Rigidified.jSbar ι ψ g) hjb hcb hF
    (t.redC g) rfl (t.redC_verschiebungInt g) (t.redC_endAct_varpiEnd g) L hL Lb hLb hLLb

  obtain ⟨LΦ, hLΦc⟩ := hLΦ
  have hrΦ' : ∀ w', rΦ w' ∈ (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).eta LΦ hLΦc.isCartierLMap.map_verschiebung :=
    fun w' => (AddSubgroup.mem_inf.mp ((hrΦ LΦ hLΦc).mapsTo (Set.mem_univ w'))).1
  have hy_eta : p • Rigidified.rigidNum ι hcΦ rΦ ψ t hOD g hcb hcΦg w ∈ ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).eta Lb hLb.isCartierLMap.map_verschiebung :=
    CerednikDrinfeld.SpecialFormal.Rigidified.nsmul_rigidNum_mem_eta ι hcΦ rΦ LΦ hLΦc.isCartierLMap hrΦ' ψ t hOD g hcb hcΦg
      Lb hLb.isCartierLMap w

  have hjj : Rigidified.jPhiS ι ψ g = Rigidified.jSbar ι ψ g := RingHom.ext fun x => rfl
  let fΦ : CartierModule p Φ.F →+ CartierModule p (t.XbarS g).F :=
    (Rigidified.rhoC ψ t hOD.1 g).comp (Rigidified.bcPhi (Φ := Φ) ψ g)
  have hfV : ∀ x, fΦ ((Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).verschiebung x) = ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).verschiebung (fΦ x) := fun x => by
    show Rigidified.rhoC ψ t hOD.1 g (Rigidified.bcPhi (Φ := Φ) ψ g (verschiebungInt x)) =
      verschiebungInt (Rigidified.rhoC ψ t hOD.1 g (Rigidified.bcPhi (Φ := Φ) ψ g x))
    rw [Rigidified.bcPhi_verschiebungInt, Rigidified.rhoC_verschiebungInt]
  have hfPi : ∀ x, fΦ ((Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).varpi x) = ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).varpi (fΦ x) := fun x => by
    show Rigidified.rhoC ψ t hOD.1 g (Rigidified.bcPhi (Φ := Φ) ψ g (endAct Φ.varpiEnd x)) =
      endAct (t.XbarS g).varpiEnd (Rigidified.rhoC ψ t hOD.1 g (Rigidified.bcPhi (Φ := Φ) ψ g x))
    rw [Rigidified.bcPhi_endAct_varpiEnd, Rigidified.rhoC_endAct_varpiEnd ψ t hOD g]
  have hfpc : ∀ (i : Fin 2) (x : CartierModule p Φ.F), x ∈ (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).piece i →
      fΦ x ∈ ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).piece i := by
    intro i x hx
    have hx' : x ∈ Φ.gradedPiece (Rigidified.jbar ι) i :=
      (FormalODModule.mem_toGradedCartierModuleData_piece_iff _ _ hcΦ i _).mp hx
    have h1 := CerednikDrinfeld.FormalODModule.baseChange_mem_gradedPiece (residueMap ψ) Φ (Rigidified.jbar ι) i hx'
    have h2 := CerednikDrinfeld.FormalODModule.baseChange_mem_gradedPiece (reduceMap (p := p) g) _ _ i h1
    have h3 := CerednikDrinfeld.FormalODModule.IsODHom.map_mem_gradedPiece p (Rigidified.jPhiS ι ψ g)
      (Rigidified.PhibarS (Φ := Φ) ψ g) (t.XbarS g) _ (hOD.map (reduceMap (p := p) g)) i _ h2
    rw [hjj] at h3
    exact (FormalODModule.mem_toGradedCartierModuleData_piece_iff _ _ hcb i _).mpr h3
  have key : Rigidified.rigidNum ι hcΦ rΦ ψ t hOD g hcb hcΦg w =
      (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).nMap ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb) fΦ hfV hfPi (rΦ w) := by
    obtain ⟨⟨a, b⟩, hab⟩ := (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).nMk_surjective (rΦ w)
    show (((Rigidified.PhibarS (Φ := Φ) ψ g).toGradedCartierModuleData (Rigidified.jPhiS ι ψ g) hcΦg).nMap ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb)
        (Rigidified.rhoC ψ t hOD.1 g) (Rigidified.rhoC_verschiebungInt ψ t hOD.1 g)
        (Rigidified.rhoC_endAct_varpiEnd ψ t hOD g))
      (((Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).nMap
        ((Rigidified.PhibarS (Φ := Φ) ψ g).toGradedCartierModuleData (Rigidified.jPhiS ι ψ g) hcΦg)
        (Rigidified.bcPhi (Φ := Φ) ψ g) (Rigidified.bcPhi_verschiebungInt (Φ := Φ) ψ g)
        (Rigidified.bcPhi_endAct_varpiEnd (Φ := Φ) ψ g)) (rΦ w)) = _
    rw [← hab, nMap_nMk, nMap_nMk, nMap_nMk]
    rfl
  have hrw0 : rΦ w ∈ (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).nPiece 0 :=
    (AddSubgroup.mem_inf.mp ((hrΦ LΦ hLΦc).mapsTo (Set.mem_univ w))).2
  have hy_piece : p • Rigidified.rigidNum ι hcΦ rΦ ψ t hOD g hcb hcΦg w ∈ ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).nPiece 0 := by
    refine AddSubgroup.nsmul_mem _ ?_ _
    rw [key]
    exact nMap_mem_nPiece (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ) ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb) fΦ hfV hfPi hfpc 0 (rΦ w) hrw0

  obtain ⟨z, hz, hzy⟩ := hbij.surjOn hy_eta
  obtain ⟨z₀, hz₀, z₁, hz₁, hzz⟩ :=
    CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.exists_mem_etaPiece_add_eq p _ ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc) L hL z hz
  have hred_piece : ∀ (m : Fin 2) (u : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).NMod), u ∈ ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nPiece m →
      ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nMap ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb) (t.redC g) (t.redC_verschiebungInt g) (t.redC_endAct_varpiEnd g) u ∈ ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).nPiece m :=
    fun m u hu => nMap_mem_nPiece ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc) ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb) _ _ _ hbca.2.2.2.2.1 m u hu
  have h0 := hred_piece 0 z₀ (AddSubgroup.mem_inf.mp hz₀).2
  have h1 := hred_piece 1 z₁ (AddSubgroup.mem_inf.mp hz₁).2
  have hNb := CerednikDrinfeld.GradedCartierModuleData.isCompl_nPiece_zero_one p _ ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb)
  have hsum : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nMap ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb) (t.redC g) (t.redC_verschiebungInt g) (t.redC_endAct_varpiEnd g) z₀ +
      ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nMap ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb) (t.redC g) (t.redC_verschiebungInt g) (t.redC_endAct_varpiEnd g) z₁ =
      p • Rigidified.rigidNum ι hcΦ rΦ ψ t hOD g hcb hcΦg w := by
    rw [← map_add, ← hzz]; exact hzy
  have h1' : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nMap ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb) (t.redC g) (t.redC_verschiebungInt g) (t.redC_endAct_varpiEnd g) z₁ ∈ ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).nPiece 0 := by
    have : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nMap ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb) (t.redC g) (t.redC_verschiebungInt g) (t.redC_endAct_varpiEnd g) z₁ =
        p • Rigidified.rigidNum ι hcΦ rΦ ψ t hOD g hcb hcΦg w -
        ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nMap ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb) (t.redC g) (t.redC_verschiebungInt g) (t.redC_endAct_varpiEnd g) z₀ := by
      rw [← hsum]; abel
    rw [this]; exact AddSubgroup.sub_mem _ hy_piece h0
  have hz1red : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nMap ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb) (t.redC g) (t.redC_verschiebungInt g) (t.redC_endAct_varpiEnd g) z₁ = 0 := by
    have := AddSubgroup.mem_inf.mpr ⟨h1', h1⟩
    rwa [hNb.inf_eq_bot, AddSubgroup.mem_bot] at this
  have hz1 : z₁ = 0 := by
    apply hbij.injOn (AddSubgroup.mem_inf.mp hz₁).1 (AddSubgroup.zero_mem _)
    rw [hz1red, map_zero]
  refine ⟨z₀, hz₀, ?_⟩
  show ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nMap ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb) (t.redC g) (t.redC_verschiebungInt g) (t.redC_endAct_varpiEnd g) z₀ = _
  rw [← hsum, hz1, map_zero, add_zero]

theorem solution
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    (Φ : FormalODModule p (O ⧸ pIdeal p O))
    (hΦ : Φ.IsSpecial (Rigidified.jbar ι)) (hΦ4 : Φ.HasHeight 4)
    (h0Φ : Φ.lieZero (Rigidified.jbar ι) ≤ LinearMap.ker Φ.lieVarpi)
    (hcΦ : IsCompl (Φ.gradedPiece (Rigidified.jbar ι) 0) (Φ.gradedPiece (Rigidified.jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
    (hLΦ : ∃ L : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).M →+
        (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod,
      (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).IsCanonicalLMap L)
    (hrΦ : ∀ (L : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).M →+
        (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
      (hL : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).IsCanonicalLMap L),
      Set.BijOn rΦ Set.univ
        ((Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).etaPiece L
          hL.isCartierLMap.map_verschiebung 0 : Set _))
    {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : O →+* B)
    (hB : IsNilpotent (p : B))
    (t : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ)
    (i : Fin 2) {S : Type} [CommRing S] [Algebra ℤ_[p] S] (g : B →+* S) (hS : IsNilpotent (p : S))
    (hc : t.IsGradedS ι ψ g) (hcb : t.IsGradedSbar ι ψ g) (hcΦg : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ g)
    (L : _) (hL : ((t.XS g).toGradedCartierModuleData _ hc).IsCanonicalLMap L)
    (w : Fin 2 → ℤ_[p]) :
    ∃ z, t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 g hc hcb hcΦg L hL i z
      ((p : ℚ_[p]) ^ (t.n + 1) • fun j => ((w j : ℤ_[p]) : ℚ_[p])) := by
  obtain ⟨z₀, hz0, hzred⟩ := W1_core p ι Φ hcΦ rΦ hLΦ hrΦ ψ t ht.2.2.1 g hS hc hcb hcΦg L hL w
  have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  rcases hi with rfl | rfl
  · refine ⟨z₀, ?_⟩
    rw [Rigidified.isEtaSection_zero_iff]
    refine ⟨hz0, 0, 0, (p ^ (t.n + 1) : ℕ) • w, ?_, ?_⟩
    · funext j
      simp only [pow_zero, Pi.smul_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_pow,
        PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast, one_mul]
    · rw [pow_zero, one_smul, map_nsmul, zero_add, add_zero, hzred, smul_smul, ← pow_succ]
  · refine ⟨((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nVarpi z₀, ?_⟩
    rw [Rigidified.isEtaSection_one_iff]
    refine ⟨?_, 0, 0, (p ^ (t.n + 2) : ℕ) • w, ?_, ?_⟩
    · have := ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).QXA_nVarpi_mem_etaPiece hL hz0
      simpa using this
    · funext j
      simp only [pow_zero, Pi.smul_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_pow,
        PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast, one_mul]
      ring
    · rw [pow_zero, one_smul, map_nsmul, zero_add, add_zero,
        ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).QXA_nVarpi_nVarpi, map_nsmul, hzred,
        smul_smul, smul_smul, ← pow_succ, ← pow_succ]

end S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isEtaSection_pow_smul_of_isAdmissible
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isEtaSection_pow_smul_of_isAdmissible (solution)
