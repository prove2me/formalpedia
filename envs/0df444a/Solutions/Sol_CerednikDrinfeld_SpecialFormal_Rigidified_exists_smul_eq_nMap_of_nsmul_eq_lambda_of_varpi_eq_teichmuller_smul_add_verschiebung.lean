-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.exists_smul_eq_nMap_of_nsmul_eq_lambda_of_varpi_eq_teichmuller_smul_add_verschiebung
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/c6c819a1-6dd1-5680-b03c-9cca10ce3442

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isSpecialCartierModule_toGradedCartierModuleData
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isHomogeneousVBasis_of_isHomogeneousVBasis_toGradedCartierModuleData
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isBaseChangeAlong_toGradedCartierModuleData_baseChange
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isCanonicalLMap_toGradedCartierModuleData
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isCompl_gradedPiece_zero_one_of_isNilpotent
import Theorems.Thm_CerednikDrinfeld_FormalODModule_IsSpecial_map
import Theorems.Thm_CerednikDrinfeld_FormalODModule_hasKernelOfDegree_map
import Theorems.Thm_CerednikDrinfeld_FormalODModule_eq_zero_of_endAct_varpiEnd_eq_zero_of_isReduced
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isCanonicalLMap_apply_eq_nMk_of_charP
import Theorems.Thm_CerednikDrinfeld_FormalODModule_mem_etaPiece_iff_of_isCanonicalLMap_apply_eq_nMk_of_charP
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_exists_digits_mem_sq_of_varpi_eq_verschiebung
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_exists_varpi_eq_teichmuller_smul_add_verschiebung_mul_eq
import Theorems.Thm_Ideal_exists_not_mem_and_forall_mul_eq_zero_of_le_sq_of_le
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_exists_digit_eq_mul_pow_add_mul_of_varpi_eq_verschiebung
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_exists_eq_varpi_add_verschiebung_iff_dvd_of_varpi_eq_teichmuller_smul_add
import Theorems.Thm_CerednikDrinfeld_FormalODModule_bijOn_lambda_etaPiece_of_isCanonicalLMap_of_forall_exists_of_charP
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_IsCanonicalLMap_comp_eq_nMap_comp_of_comp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_smul_eq_nMap_of_nsmul_eq_lambda_of_varpi_eq_teichmuller_smul_add_verschiebung
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt"

set_option autoImplicit false

p2m_open "CerednikDrinfeld P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_smul_eq_nMap_of_nsmul_eq_lambda_of_varpi_eq_teichmuller_smul_add_verschiebung.CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega"

open scoped PadicInt Padic

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "Zp2 SpecialFormal.Series SpecialFormal.Series.map_map FormalODModule FormalODModule.map_act FormalODModule.map_map FormalODModule.IsSpecial FormalODModule.KerAlgebra FormalODModule.HasKernelOfDegree FormalODModule.F GradedCartierModuleData GradedCartierModuleData.IsCanonicalLMap FormalODModule.isSpecialCartierModule_toGradedCartierModuleData FormalODModule.isHomogeneousVBasis_of_isHomogeneousVBasis_toGradedCartierModuleData FormalODModule.isBaseChangeAlong_toGradedCartierModuleData_baseChange FormalODModule.exists_isCanonicalLMap_toGradedCartierModuleData FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent FormalODModule.IsSpecial.map FormalODModule.hasKernelOfDegree_map FormalODModule.isCanonicalLMap_apply_eq_nMk_of_charP GradedCartierModuleData.exists_digit_eq_mul_pow_add_mul_of_varpi_eq_verschiebung GradedCartierModuleData.exists_eq_varpi_add_verschiebung_iff_dvd_of_varpi_eq_teichmuller_smul_add FormalODModule.bijOn_lambda_etaPiece_of_isCanonicalLMap_of_forall_exists_of_charP GradedCartierModuleData.IsCanonicalLMap.comp_eq_nMap_comp_of_comp_eq"
namespace GradedCartierModuleData
p2m_export "CerednikDrinfeld.GradedCartierModuleData" "IsHomogeneousVBasis isCompl_piece varpi_varpi varpi M verschiebung_mem frobenius piece verschiebung varpi_mem smul_verschiebung varpi_verschiebung varpi_frobenius NMod nMk nMk_surjective nMk_verschiebung_neg_varpi smul_nMk lambda lambda_nMk nVarpi nPiece nMap nMap_nMk IsBaseChangeAlong' IsCartierLMap IsCanonicalLMap phi phi_nMk mem_eta_iff etaPiece u exists_digit_eq_mul_pow_add_mul_of_varpi_eq_verschiebung exists_eq_varpi_add_verschiebung_iff_dvd_of_varpi_eq_teichmuller_smul_add IsCanonicalLMap.comp_eq_nMap_comp_of_comp_eq"
p2m_open "CerednikDrinfeld.GradedCartierModuleData CerednikDrinfeld"

variable {p : ℕ} [Fact p.Prime]
variable {B B' : Type} [CommRing B] [CommRing B'] {j : Zp2 p →+* B} {j' : Zp2 p →+* B'}

theorem R1a_nsmul_eq_zero_of_lambda_eq_zero (D : GradedCartierModuleData p B j) (z : D.NMod)
    (hz : D.lambda z = 0) : (p : ℕ) • z = 0 := by
  obtain ⟨⟨a, b⟩, rfl⟩ := D.nMk_surjective z
  rw [lambda_nMk] at hz
  have ha' : D.varpi a = -D.verschiebung b := eq_neg_of_add_eq_zero_left hz
  have h1 : (p : ℕ) • a = D.verschiebung (-D.varpi b) := by
    rw [← D.varpi_varpi, ha', map_neg, map_neg, D.varpi_verschiebung]
  have h2 : (p : ℕ) • b = -D.varpi (-D.varpi b) := by
    rw [map_neg, neg_neg, D.varpi_varpi]
  rw [← map_nsmul, Prod.smul_mk, h1, h2]
  exact D.nMk_verschiebung_neg_varpi _

private theorem _root_.CerednikDrinfeld.GradedCartierModuleData.R1a_lambda_nMap (D : GradedCartierModuleData p B j) (D' : GradedCartierModuleData p B' j')
    (f : D.M →+ D'.M) (hV : ∀ x, f (D.verschiebung x) = D'.verschiebung (f x))
    (hPi : ∀ x, f (D.varpi x) = D'.varpi (f x)) (z : D.NMod) :
    D'.lambda (D.nMap D' f hV hPi z) = f (D.lambda z) := by
  obtain ⟨⟨a, b⟩, rfl⟩ := D.nMk_surjective z
  rw [nMap_nMk, lambda_nMk, lambda_nMk, map_add, hPi, hV]

p2m_export "CerednikDrinfeld.GradedCartierModuleData" "R1a_lambda_nMap"

theorem R1a_nsmul_eq_zero_of_nMap_eq_zero (D : GradedCartierModuleData p B j) (D' : GradedCartierModuleData p B' j')
    (f : D.M →+ D'.M) (hV : ∀ x, f (D.verschiebung x) = D'.verschiebung (f x))
    (hPi : ∀ x, f (D.varpi x) = D'.varpi (f x)) (hf : Function.Injective f)
    (z : D.NMod) (hz : D.nMap D' f hV hPi z = 0) : (p : ℕ) • z = 0 := by
  apply R1a_nsmul_eq_zero_of_lambda_eq_zero
  apply hf
  rw [← R1a_lambda_nMap D D' f hV hPi, hz, map_zero, map_zero]

private theorem _root_.CerednikDrinfeld.GradedCartierModuleData.R1a_nVarpi_nMk (D : GradedCartierModuleData p B j) (m m' : D.M) :
    D.nVarpi (D.nMk (m, m')) = D.nMk (D.varpi m, D.varpi m') := rfl

p2m_export "CerednikDrinfeld.GradedCartierModuleData" "R1a_nVarpi_nMk"
theorem R1a_lambda_nVarpi (D : GradedCartierModuleData p B j) (z : D.NMod) :
    D.lambda (D.nVarpi z) = D.varpi (D.lambda z) := by
  obtain ⟨⟨m, m'⟩, rfl⟩ := D.nMk_surjective z
  rw [R1a_nVarpi_nMk, lambda_nMk, lambda_nMk, map_add, D.varpi_verschiebung]

private theorem _root_.CerednikDrinfeld.GradedCartierModuleData.R1a_nVarpi_mem_nPiece (D : GradedCartierModuleData p B j) {i : Fin 2} {z : D.NMod}
    (hz : z ∈ D.nPiece i) : D.nVarpi z ∈ D.nPiece (i + 1) := by
  obtain ⟨⟨m, m'⟩, hmm, rfl⟩ := hz
  exact ⟨(D.varpi m, D.varpi m'), ⟨D.varpi_mem i m hmm.1, D.varpi_mem i m' hmm.2⟩,
    (D.R1a_nVarpi_nMk m m').symm⟩

p2m_export "CerednikDrinfeld.GradedCartierModuleData" "R1a_nVarpi_mem_nPiece"
private theorem _root_.CerednikDrinfeld.GradedCartierModuleData.R1a_nMap_mem_nPiece (D : GradedCartierModuleData p B j) (D' : GradedCartierModuleData p B' j')
    (f : D.M →+ D'.M) (hV : ∀ x, f (D.verschiebung x) = D'.verschiebung (f x))
    (hPi : ∀ x, f (D.varpi x) = D'.varpi (f x))
    (hpc : ∀ (i : Fin 2) (x : D.M), x ∈ D.piece i → f x ∈ D'.piece i)
    (m : Fin 2) (n : D.NMod) (hn : n ∈ D.nPiece m) : D.nMap D' f hV hPi n ∈ D'.nPiece m := by
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := AddSubgroup.mem_map.mp hn
  obtain ⟨ha, hb⟩ := AddSubgroup.mem_prod.mp hab
  rw [nMap_nMk]
  exact AddSubgroup.mem_map.mpr ⟨(f a, f b), AddSubgroup.mem_prod.mpr ⟨hpc m a ha, hpc m b hb⟩, rfl⟩

p2m_export "CerednikDrinfeld.GradedCartierModuleData" "R1a_nMap_mem_nPiece"

theorem R1a_nsmul_phi_nVarpi (D : GradedCartierModuleData p B j) {L : D.M →+ D.NMod} (hL : D.IsCartierLMap L)
    (w : D.NMod) :
    (p : ℕ) • D.phi L hL.map_verschiebung (D.nVarpi w) = (p : ℕ) • D.nVarpi (D.phi L hL.map_verschiebung w) := by
  obtain ⟨⟨x, x'⟩, rfl⟩ := D.nMk_surjective w
  rw [R1a_nVarpi_nMk, phi_nMk, phi_nMk, map_add, R1a_nVarpi_nMk, map_zero, nsmul_add, nsmul_add,
    ← sub_eq_zero, add_sub_add_right_eq_sub, ← nsmul_sub]
  apply R1a_nsmul_eq_zero_of_lambda_eq_zero
  rw [map_sub, R1a_lambda_nVarpi, hL.lambda_comp, hL.lambda_comp, D.varpi_frobenius, sub_self]

theorem R1a_nsmul_nVarpi_mem_etaPiece (D : GradedCartierModuleData p B j) {L : D.M →+ D.NMod}
    (hL : D.IsCartierLMap L) {i : Fin 2} {z : D.NMod} (hz : z ∈ D.etaPiece L hL.map_verschiebung i) :
    (p : ℕ) • D.nVarpi z ∈ D.etaPiece L hL.map_verschiebung (i + 1) := by
  obtain ⟨hz1, hz2⟩ := AddSubgroup.mem_inf.1 hz
  refine AddSubgroup.mem_inf.2 ⟨?_, AddSubgroup.nsmul_mem _ (D.R1a_nVarpi_mem_nPiece hz2) _⟩
  rw [mem_eta_iff] at hz1 ⊢
  rw [map_nsmul, R1a_nsmul_phi_nVarpi D hL, hz1]

theorem R1a_nsmul_phi_nMap (D : GradedCartierModuleData p B j) (D' : GradedCartierModuleData p B' j')
    (f : D.M →+ D'.M) (hF : ∀ x, f (D.frobenius x) = D'.frobenius (f x))
    (hV : ∀ x, f (D.verschiebung x) = D'.verschiebung (f x))
    (hPi : ∀ x, f (D.varpi x) = D'.varpi (f x))
    {L : D.M →+ D.NMod} (hL : D.IsCartierLMap L) {L' : D'.M →+ D'.NMod} (hL' : D'.IsCartierLMap L')
    (w : D.NMod) :
    (p : ℕ) • D'.phi L' hL'.map_verschiebung (D.nMap D' f hV hPi w) =
      (p : ℕ) • D.nMap D' f hV hPi (D.phi L hL.map_verschiebung w) := by
  obtain ⟨⟨x, x'⟩, rfl⟩ := D.nMk_surjective w
  rw [nMap_nMk, phi_nMk, phi_nMk, map_add, nMap_nMk, map_zero, nsmul_add, nsmul_add,
    ← sub_eq_zero, add_sub_add_right_eq_sub, ← nsmul_sub]
  apply R1a_nsmul_eq_zero_of_lambda_eq_zero
  rw [map_sub, hL'.lambda_comp, R1a_lambda_nMap, hL.lambda_comp, hF, sub_self]

theorem R1a_phi_nsmul_eq_of_phi_nMap_eq (D : GradedCartierModuleData p B j) (D' : GradedCartierModuleData p B' j')
    (f : D.M →+ D'.M) (hF : ∀ x, f (D.frobenius x) = D'.frobenius (f x))
    (hV : ∀ x, f (D.verschiebung x) = D'.verschiebung (f x))
    (hPi : ∀ x, f (D.varpi x) = D'.varpi (f x)) (hf : Function.Injective f)
    {L : D.M →+ D.NMod} (hL : D.IsCartierLMap L) {L' : D'.M →+ D'.NMod} (hL' : D'.IsCartierLMap L')
    (x₀ : D.NMod)
    (hfix : D'.phi L' hL'.map_verschiebung (D.nMap D' f hV hPi x₀) = D.nMap D' f hV hPi x₀) :
    D.phi L hL.map_verschiebung ((p ^ 2 : ℕ) • x₀) = (p ^ 2 : ℕ) • x₀ := by
  have h1 : (p : ℕ) • ((p : ℕ) • (D.phi L hL.map_verschiebung x₀ - x₀)) = 0 := by
    apply R1a_nsmul_eq_zero_of_nMap_eq_zero D D' f hV hPi hf
    rw [map_nsmul, map_sub, nsmul_sub, ← R1a_nsmul_phi_nMap D D' f hF hV hPi hL hL', hfix, sub_self]
  rw [smul_smul, ← pow_two, nsmul_sub, sub_eq_zero] at h1
  rw [map_nsmul, h1]

private theorem _root_.CerednikDrinfeld.GradedCartierModuleData.R1a_phi_nMap_of_comp (D : GradedCartierModuleData p B j) (D' : GradedCartierModuleData p B' j')
    (f : D.M →+ D'.M) (hV : ∀ x, f (D.verschiebung x) = D'.verschiebung (f x))
    (hPi : ∀ x, f (D.varpi x) = D'.varpi (f x))
    {L : D.M →+ D.NMod} (hL : ∀ x, L (D.verschiebung x) = D.nMk (D.varpi x, 0))
    {L' : D'.M →+ D'.NMod} (hL' : ∀ x, L' (D'.verschiebung x) = D'.nMk (D'.varpi x, 0))
    (hLL : ∀ x, L' (f x) = D.nMap D' f hV hPi (L x)) (w : D.NMod) :
    D'.phi L' hL' (D.nMap D' f hV hPi w) = D.nMap D' f hV hPi (D.phi L hL w) := by
  obtain ⟨⟨x, x'⟩, rfl⟩ := D.nMk_surjective w
  rw [nMap_nMk, phi_nMk, phi_nMk, map_add, nMap_nMk, hLL, map_zero]

p2m_export "CerednikDrinfeld.GradedCartierModuleData" "R1a_phi_nMap_of_comp"

theorem R1a_exists_nMap_eq_nsmul (D : GradedCartierModuleData p B j) (D' : GradedCartierModuleData p B' j')
    (f : D.M →+ D'.M) (hV : ∀ x, f (D.verschiebung x) = D'.verschiebung (f x))
    (hPi : ∀ x, f (D.varpi x) = D'.varpi (f x))
    (hc : ∀ m : D'.M, ∃ (a : ℕ) (m₀ : D.M), f m₀ = (p ^ a : ℕ) • m) (w : D'.NMod) :
    ∃ (a : ℕ) (w₀ : D.NMod), D.nMap D' f hV hPi w₀ = (p ^ a : ℕ) • w := by
  obtain ⟨⟨m₁, m₂⟩, rfl⟩ := D'.nMk_surjective w
  obtain ⟨a₁, n₁, h₁⟩ := hc m₁
  obtain ⟨a₂, n₂, h₂⟩ := hc m₂
  refine ⟨a₁ + a₂, D.nMk ((p ^ a₂ : ℕ) • n₁, (p ^ a₁ : ℕ) • n₂), ?_⟩
  rw [nMap_nMk, map_nsmul, map_nsmul, h₁, h₂, smul_smul, smul_smul, ← pow_add, ← pow_add,
    add_comm a₂ a₁, ← map_nsmul, Prod.smul_mk]

end CerednikDrinfeld.GradedCartierModuleData

noncomputable section

namespace StratumDescent

p2m_open "CerednikDrinfeld P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_smul_eq_nMap_of_nsmul_eq_lambda_of_varpi_eq_teichmuller_smul_add_verschiebung.CerednikDrinfeld CerednikDrinfeld.GradedCartierModuleData P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_smul_eq_nMap_of_nsmul_eq_lambda_of_varpi_eq_teichmuller_smul_add_verschiebung.CerednikDrinfeld.GradedCartierModuleData MvFormalGroup MvFormalGroup.CartierModule"

section Datum

variable {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] {j : Zp2 p →+* B}
  (D : GradedCartierModuleData p B j)

theorem exists_eq_teichmuller_smul_add_verschiebung {γ : Fin 2 → D.M} (hγ : D.IsHomogeneousVBasis γ)
    (i : Fin 2) (x : D.M) (hx : x ∈ D.piece i) :
    ∃ (c : B) (m : D.M), x = WittVector.teichmuller p c • γ i + D.verschiebung m := by
  classical
  obtain ⟨⟨c, y⟩, hcy, -⟩ := hγ.2 x

  have hsup : D.piece 0 ⊔ D.piece 1 = ⊤ := D.isCompl_piece.sup_eq_top
  have hy : y ∈ D.piece 0 ⊔ D.piece 1 := by rw [hsup]; exact Submodule.mem_top
  obtain ⟨y0, hy0, y1, hy1, rfl⟩ := Submodule.mem_sup.1 hy

  fin_cases i
  ·
    have hdec : x = (WittVector.teichmuller p (c 0) • γ 0 + D.verschiebung y1) +
        (WittVector.teichmuller p (c 1) • γ 1 + D.verschiebung y0) := by
      rw [hcy, Fin.sum_univ_two, map_add]; abel
    have h0 : WittVector.teichmuller p (c 0) • γ 0 + D.verschiebung y1 ∈ D.piece 0 :=
      Submodule.add_mem _ (Submodule.smul_mem _ _ (hγ.1 0)) (by simpa using D.verschiebung_mem 1 y1 hy1)
    have h1 : WittVector.teichmuller p (c 1) • γ 1 + D.verschiebung y0 ∈ D.piece 1 :=
      Submodule.add_mem _ (Submodule.smul_mem _ _ (hγ.1 1)) (by simpa using D.verschiebung_mem 0 y0 hy0)
    have hz : WittVector.teichmuller p (c 1) • γ 1 + D.verschiebung y0 ∈ D.piece 0 := by
      have : x - (WittVector.teichmuller p (c 0) • γ 0 + D.verschiebung y1) ∈ D.piece 0 := Submodule.sub_mem _ hx h0
      rwa [hdec, add_sub_cancel_left] at this
    have hzero : WittVector.teichmuller p (c 1) • γ 1 + D.verschiebung y0 = 0 := by
      have := D.isCompl_piece.disjoint
      rw [Submodule.disjoint_def] at this
      exact this _ hz h1
    refine ⟨c 0, y1, ?_⟩
    rw [hdec, hzero, add_zero]
    rfl
  · have hdec : x = (WittVector.teichmuller p (c 1) • γ 1 + D.verschiebung y0) +
        (WittVector.teichmuller p (c 0) • γ 0 + D.verschiebung y1) := by
      rw [hcy, Fin.sum_univ_two, map_add]; abel
    have h1 : WittVector.teichmuller p (c 1) • γ 1 + D.verschiebung y0 ∈ D.piece 1 :=
      Submodule.add_mem _ (Submodule.smul_mem _ _ (hγ.1 1)) (by simpa using D.verschiebung_mem 0 y0 hy0)
    have h0 : WittVector.teichmuller p (c 0) • γ 0 + D.verschiebung y1 ∈ D.piece 0 :=
      Submodule.add_mem _ (Submodule.smul_mem _ _ (hγ.1 0)) (by simpa using D.verschiebung_mem 1 y1 hy1)
    have hz : WittVector.teichmuller p (c 0) • γ 0 + D.verschiebung y1 ∈ D.piece 1 := by
      have : x - (WittVector.teichmuller p (c 1) • γ 1 + D.verschiebung y0) ∈ D.piece 1 := Submodule.sub_mem _ hx h1
      rwa [hdec, add_sub_cancel_left] at this
    have hzero : WittVector.teichmuller p (c 0) • γ 0 + D.verschiebung y1 = 0 := by
      have := D.isCompl_piece.disjoint
      rw [Submodule.disjoint_def] at this
      exact this _ h0 hz
    refine ⟨c 1, y0, ?_⟩
    rw [hdec, hzero, add_zero]
    rfl

theorem teichmuller_coeff_unique {γ : Fin 2 → D.M} (hγ : D.IsHomogeneousVBasis γ)
    (c c' : Fin 2 → B) (y y' : D.M)
    (h : (∑ i : Fin 2, WittVector.teichmuller p (c i) • γ i) + D.verschiebung y =
      (∑ i : Fin 2, WittVector.teichmuller p (c' i) • γ i) + D.verschiebung y') :
    c = c' ∧ y = y' := by
  obtain ⟨cy, -, huniq⟩ := hγ.2 ((∑ i : Fin 2, WittVector.teichmuller p (c i) • γ i) + D.verschiebung y)
  have h1 : (c, y) = cy := huniq (c, y) rfl
  have h2 : (c', y') = cy := huniq (c', y') h
  have := h1.trans h2.symm
  exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩

theorem fin_two_add_one_add_one (l : Fin 2) : l + 1 + 1 = l := by
  fin_cases l <;> rfl

theorem exists_piece_split (l : Fin 2) (g : D.M) :
    ∃ g₁ ∈ D.piece l, ∃ g₂ ∈ D.piece (l + 1), g = g₁ + g₂ := by
  have hsup : D.piece 0 ⊔ D.piece 1 = ⊤ := D.isCompl_piece.sup_eq_top
  have hg : g ∈ D.piece 0 ⊔ D.piece 1 := by rw [hsup]; exact Submodule.mem_top
  obtain ⟨g0, hg0, g1, hg1, rfl⟩ := Submodule.mem_sup.1 hg
  fin_cases l
  · exact ⟨g0, hg0, g1, hg1, rfl⟩
  · exact ⟨g1, hg1, g0, hg0, add_comm _ _⟩

theorem eq_zero_of_mem_piece_of_mem_piece_add_one (l : Fin 2) (m : D.M) (h₁ : m ∈ D.piece l)
    (h₂ : m ∈ D.piece (l + 1)) : m = 0 := by
  have hd := D.isCompl_piece.disjoint
  rw [Submodule.disjoint_def] at hd
  fin_cases l
  · exact hd _ h₁ h₂
  · exact hd _ h₂ h₁

theorem mem_piece_of_verschiebung_mem (hV : Function.Injective D.verschiebung) (l : Fin 2) (g : D.M)
    (hg : D.verschiebung g ∈ D.piece (l + 1)) : g ∈ D.piece l := by
  obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := exists_piece_split D l g
  have h2 : D.verschiebung g₂ ∈ D.piece l := by
    have := D.verschiebung_mem (l + 1) g₂ hg₂
    rwa [fin_two_add_one_add_one] at this
  have h2' : D.verschiebung g₂ ∈ D.piece (l + 1) := by
    have h1 : D.verschiebung g₁ ∈ D.piece (l + 1) := D.verschiebung_mem l g₁ hg₁
    have := Submodule.sub_mem _ hg h1
    rwa [map_add, add_sub_cancel_left] at this
  have hz : D.verschiebung g₂ = 0 := eq_zero_of_mem_piece_of_mem_piece_add_one D l _ h2 h2'
  have : g₂ = 0 := hV (by rw [hz, map_zero])
  rw [this, add_zero]
  exact hg₁

theorem exists_eq_teichmuller_smul_add_verschiebung' {γ : Fin 2 → D.M} (hγ : D.IsHomogeneousVBasis γ)
    (i : Fin 2) (x : D.M) (hx : x ∈ D.piece i) :
    ∃ (c : B) (m : D.M), m ∈ D.piece (i + 1) ∧ x = WittVector.teichmuller p c • γ i + D.verschiebung m := by
  obtain ⟨c, m, hxm⟩ := exists_eq_teichmuller_smul_add_verschiebung D hγ i x hx
  refine ⟨c, m, ?_, hxm⟩
  apply mem_piece_of_verschiebung_mem D hγ.verschiebung_injective
  rw [fin_two_add_one_add_one]
  have := Submodule.sub_mem _ hx (Submodule.smul_mem _ (WittVector.teichmuller p c) (hγ.1 i))
  rwa [hxm, add_sub_cancel_left] at this

theorem mem_nPiece_iff (l : Fin 2) (z : D.NMod) :
    z ∈ D.nPiece l ↔ ∃ m m' : D.M, m ∈ D.piece l ∧ m' ∈ D.piece l ∧ D.nMk (m, m') = z := by
  constructor
  · rintro ⟨⟨m, m'⟩, hmm, rfl⟩
    exact ⟨m, m', hmm.1, hmm.2, rfl⟩
  · rintro ⟨m, m', hm, hm', rfl⟩
    exact ⟨(m, m'), ⟨hm, hm'⟩, rfl⟩

theorem nMk_mem_nPiece (l : Fin 2) {m m' : D.M} (hm : m ∈ D.piece l) (hm' : m' ∈ D.piece l) :
    D.nMk (m, m') ∈ D.nPiece l :=
  (mem_nPiece_iff D l _).2 ⟨m, m', hm, hm', rfl⟩

theorem smul_mem_nPiece (l : Fin 2) (w : WittVector p B) {z : D.NMod} (hz : z ∈ D.nPiece l) :
    w • z ∈ D.nPiece l := by
  obtain ⟨m, m', hm, hm', rfl⟩ := (mem_nPiece_iff D l z).1 hz
  rw [smul_nMk]
  exact nMk_mem_nPiece D l (Submodule.smul_mem _ _ hm) (Submodule.smul_mem _ _ hm')

theorem lambda_mem_piece (l : Fin 2) {z : D.NMod} (hz : z ∈ D.nPiece l) : D.lambda z ∈ D.piece (l + 1) := by
  obtain ⟨m, m', hm, hm', rfl⟩ := (mem_nPiece_iff D l z).1 hz
  rw [lambda_nMk]
  exact Submodule.add_mem _ (D.varpi_mem l m hm) (D.verschiebung_mem l m' hm')

theorem teichmuller_smul_eq_sum (γ : Fin 2 → D.M) (i : Fin 2) (c : B) :
    WittVector.teichmuller p c • γ i =
      ∑ r : Fin 2, WittVector.teichmuller p ((if r = i then c else 0 : B)) • γ r := by
  fin_cases i <;> simp [Fin.sum_univ_two, WittVector.teichmuller_zero]

theorem digit_unique {γ : Fin 2 → D.M} (hγ : D.IsHomogeneousVBasis γ) (i : Fin 2) (c c' : B) (y y' : D.M)
    (h : WittVector.teichmuller p c • γ i + D.verschiebung y =
      WittVector.teichmuller p c' • γ i + D.verschiebung y') : c = c' ∧ y = y' := by
  rw [teichmuller_smul_eq_sum D γ i c, teichmuller_smul_eq_sum D γ i c'] at h
  obtain ⟨hcc, hyy⟩ := teichmuller_coeff_unique D hγ _ _ y y' h
  have := congrFun hcc i
  simp only [] at this
  exact ⟨by simpa using this, hyy⟩

theorem nsmul_eq_verschiebung_verschiebung (n : D.M) (hn : D.varpi n = D.verschiebung n) :
    p • n = D.verschiebung (D.verschiebung n) := by
  rw [← D.varpi_varpi, hn, D.varpi_verschiebung, hn]

end Datum

section Law

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] (jR : Zp2 p →+* R)
  (X : FormalODModule p R) (hc : IsCompl (X.gradedPiece jR 0) (X.gradedPiece jR 1))

theorem crit_of_basis (γ : Fin 2 → (X.toGradedCartierModuleData jR hc).M)
    (hγ : (X.toGradedCartierModuleData jR hc).IsHomogeneousVBasis γ) (i : Fin 2) (xi : (X.toGradedCartierModuleData jR hc).M)
    (hcrit : (X.toGradedCartierModuleData jR hc).varpi (γ i) = (X.toGradedCartierModuleData jR hc).verschiebung xi) :
    ∀ m ∈ X.gradedPiece jR (i : ℕ), ∃ g : CartierModule p X.F, verschiebungInt g = endAct X.varpiEnd m := by
  intro m hm
  obtain ⟨c, m', hmm⟩ := exists_eq_teichmuller_smul_add_verschiebung (X.toGradedCartierModuleData jR hc) hγ i m hm
  refine ⟨(WittVector.frobenius (WittVector.teichmuller p c) • xi + (X.toGradedCartierModuleData jR hc).varpi m' :
    (X.toGradedCartierModuleData jR hc).M), ?_⟩
  have : (X.toGradedCartierModuleData jR hc).varpi m =
      (X.toGradedCartierModuleData jR hc).verschiebung
        (WittVector.frobenius (WittVector.teichmuller p c) • xi + (X.toGradedCartierModuleData jR hc).varpi m') := by
    rw [hmm, map_add, map_smul, hcrit, (X.toGradedCartierModuleData jR hc).smul_verschiebung,
      (X.toGradedCartierModuleData jR hc).varpi_verschiebung, ← map_add]
  exact this.symm

variable [CharP R p]

theorem nMk_mem_etaPiece (L : (X.toGradedCartierModuleData jR hc).M →+ (X.toGradedCartierModuleData jR hc).NMod)
    (hL : (X.toGradedCartierModuleData jR hc).IsCanonicalLMap L) (i : Fin 2)
    (hi : ∀ m ∈ X.gradedPiece jR (i : ℕ), ∃ g : CartierModule p X.F, verschiebungInt g = endAct X.varpiEnd m)
    (n : CartierModule p X.F) (hn : n ∈ X.gradedPiece jR (i : ℕ))
    (hinv : endAct X.varpiEnd n = verschiebungInt n) :
    (X.toGradedCartierModuleData jR hc).nMk (n, 0) ∈
      (X.toGradedCartierModuleData jR hc).etaPiece L hL.isCartierLMap.map_verschiebung i := by
  have hLe : L n = (X.toGradedCartierModuleData jR hc).nMk (n, 0) :=
    CerednikDrinfeld.FormalODModule.isCanonicalLMap_apply_eq_nMk_of_charP p jR X hc L hL (i : ℕ) hi n n hn hinv.symm
  refine AddSubgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [mem_eta_iff, phi_nMk, hLe, ← map_add, Prod.mk_add_mk, add_zero, zero_add]
  · exact AddSubgroup.mem_map.2 ⟨(n, 0), AddSubgroup.mem_prod.2 ⟨hn, zero_mem _⟩, rfl⟩

end Law

theorem hasHeight_map_field {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] (X : FormalODModule p B)
    (hX4 : X.HasHeight 4) {K : Type} [Field K] (g : B →+* K) : (X.map g).HasHeight 4 := by
  obtain ⟨-, -, hfib⟩ := hX4
  have hK : Module.finrank K (FormalODModule.KerAlgebra ((X.act (p : Zp2 p)).map g)) = p ^ 4 := hfib K g
  show FormalODModule.HasKernelOfDegree ((X.map g).act (p : Zp2 p)) (p ^ 4)
  rw [FormalODModule.map_act]
  refine ⟨?_, ?_, fun κ _ f => ?_⟩
  · exact Module.finite_of_finrank_pos (by rw [hK]; exact pow_pos (Nat.Prime.pos Fact.out) 4)
  · exact Module.Projective.of_free
  · rw [CerednikDrinfeld.SpecialFormal.Series.map_map]; exact hfib κ (f.comp g)

theorem isBaseChangeAlong'_of_eq {p : ℕ} [Fact p.Prime] {B S : Type} [CommRing B] [CommRing S] (j : Zp2 p →+* B)
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

theorem isHausdorff_of_eq_zero {p : ℕ} {S : Type} [CommRing S] (hS : ((p : ℕ) : S) = 0) :
    IsHausdorff (Ideal.span {((p : ℕ) : S)}) S := by
  refine ⟨fun x hx => ?_⟩
  have := hx 1
  rwa [pow_one, hS, Ideal.span_singleton_eq_bot.mpr rfl, Submodule.bot_smul, SModEq.bot] at this

end StratumDescent

end

set_option maxHeartbeats 3200000 in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
open StratumDescent _root_.CerednikDrinfeld.GradedCartierModuleData _root_.P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_smul_eq_nMap_of_nsmul_eq_lambda_of_varpi_eq_teichmuller_smul_add_verschiebung.CerednikDrinfeld.GradedCartierModuleData MvFormalGroup MvFormalGroup.CartierModule in
theorem solution
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    (Φ : FormalODModule p (O ⧸ pIdeal p O))
    {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : O →+* B) (hB : IsNilpotent (p : B))
    (t : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ)
    {S : Type} [CommRing S] [IsReduced S] [IsNoetherianRing S] (g : B →+* S) (hS : (p : S) = 0)
    (hc : t.IsGradedS ι ψ g)
    (L : ((t.XS g).toGradedCartierModuleData _ hc).M →+ ((t.XS g).toGradedCartierModuleData _ hc).NMod) (hL : ((t.XS g).toGradedCartierModuleData _ hc).IsCanonicalLMap L)
    (j : Fin 2) (γ : Fin 2 → ((t.XS g).toGradedCartierModuleData _ hc).M) (hγ : ((t.XS g).toGradedCartierModuleData _ hc).IsHomogeneousVBasis γ)
    (a : S) (ha : ∀ s : S, a * s = 0 → s = 0)
    (xj : ((t.XS g).toGradedCartierModuleData _ hc).M) (hnc : ((t.XS g).toGradedCartierModuleData _ hc).varpi (γ j) = WittVector.teichmuller p a • γ (j + 1) + ((t.XS g).toGradedCartierModuleData _ hc).verschiebung xj)
    (xj' : ((t.XS g).toGradedCartierModuleData _ hc).M) (hcrit : ((t.XS g).toGradedCartierModuleData _ hc).varpi (γ (j + 1)) = ((t.XS g).toGradedCartierModuleData _ hc).verschiebung xj')
    (z : ((t.XS g).toGradedCartierModuleData _ hc).NMod) (hz : z ∈ ((t.XS g).toGradedCartierModuleData _ hc).etaPiece L hL.isCartierLMap.map_verschiebung j)
    (x : PrimeSpectrum S)
    (m₀ : ((t.XS g).toGradedCartierModuleData _ hc).M) (hm₀ : m₀ ∈ ((t.XS g).toGradedCartierModuleData _ hc).piece (j + 1)) (hinv₀ : ((t.XS g).toGradedCartierModuleData _ hc).varpi m₀ = ((t.XS g).toGradedCartierModuleData _ hc).verschiebung m₀)
    (hpm₀ : p • m₀ = ((t.XS g).toGradedCartierModuleData _ hc).lambda z)
    (c : S) (n : ((t.XS g).toGradedCartierModuleData _ hc).M) (hdig : m₀ = WittVector.teichmuller p c • γ (j + 1) + ((t.XS g).toGradedCartierModuleData _ hc).verschiebung n)
    (hcx : a ∈ x.asIdeal → c ∈ x.asIdeal) :
    ∃ (f₀ : S) (_ : f₀ ∉ x.asIdeal) (hc₀ : t.IsGradedS ι ψ ((algebraMap S (Localization.Away f₀)).comp g))
      (L₀ : ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).M →+ ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).NMod) (hL₀ : ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).IsCanonicalLMap L₀)
      (hXr : (t.XS g).F.map (algebraMap S (Localization.Away f₀)) = (t.XS ((algebraMap S (Localization.Away f₀)).comp g)).F)
      (hrV : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXr (((t.XS g).toGradedCartierModuleData _ hc).verschiebung m) =
        ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).verschiebung (MvFormalGroup.CartierModule.baseChangeEq _ hXr m))
      (hrPi : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXr (((t.XS g).toGradedCartierModuleData _ hc).varpi m) =
        ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).varpi (MvFormalGroup.CartierModule.baseChangeEq _ hXr m))
      (z₀ : ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).NMod),
      z₀ ∈ ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).etaPiece L₀ hL₀.isCartierLMap.map_verschiebung j ∧
        p • z₀ = ((t.XS g).toGradedCartierModuleData _ hc).nMap ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀) (MvFormalGroup.CartierModule.baseChangeEq _ hXr) hrV hrPi z := by
  classical

  haveI hNontriv : Nontrivial S := nontrivial_of_ne 1 0 (fun h10 =>
    x.2.ne_top ((Ideal.eq_top_iff_one _).2 (h10.symm ▸ x.asIdeal.zero_mem)))
  haveI : CharP S p := ringChar.of_eq (CharP.ringChar_of_prime_eq_zero Fact.out hS)
  have hpS : IsNilpotent ((p : ℕ) : S) := ⟨1, by rw [pow_one, hS]⟩
  have hXS : (t.XS g).IsSpecial (Rigidified.jS ι ψ g) :=
    CerednikDrinfeld.FormalODModule.IsSpecial.map _ g t.X ht.1
  have hX4S : (t.XS g).HasHeight 4 := by
    show FormalODModule.HasKernelOfDegree ((t.X.map g).act (p : Zp2 p)) (p ^ 4)
    rw [FormalODModule.map_act]
    exact CerednikDrinfeld.FormalODModule.hasKernelOfDegree_map g _ (t.X.isLawHom_act _).1 ht.2.1
  letI : Algebra ℤ_[p] S := (g.comp (algebraMap ℤ_[p] B)).toAlgebra
  have hγS : (t.XS g).IsHomogeneousVBasis (Rigidified.jS ι ψ g) γ :=
    CerednikDrinfeld.FormalODModule.isHomogeneousVBasis_of_isHomogeneousVBasis_toGradedCartierModuleData
      p _ (t.XS g) hc γ hγ
  obtain ⟨-, hD⟩ := CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData
    p _ (t.XS g) _ hγS hc

  have hnext' : ((t.XS g).toGradedCartierModuleData _ hc).varpi (γ (j + 1 + 1)) =
      WittVector.teichmuller p a • γ (j + 1) + ((t.XS g).toGradedCartierModuleData _ hc).verschiebung xj := by
    rw [fin_two_add_one_add_one]; exact hnc
  obtain ⟨c', d, b, m₂, x', hm₀', hxi, hcrel'⟩ :=
    CerednikDrinfeld.GradedCartierModuleData.exists_digit_eq_mul_pow_add_mul_of_varpi_eq_verschiebung
      p _ ((t.XS g).toGradedCartierModuleData _ hc) γ hγ (j + 1) xj' xj a hcrit hnext' m₀ hm₀ hinv₀
  obtain ⟨hcc', hn⟩ := digit_unique ((t.XS g).toGradedCartierModuleData _ hc) hγ (j + 1) c c' n _ (hdig.symm.trans hm₀')
  have hcrel : c = b * c ^ p + a * d := by rw [hcc']; exact hcrel'

  obtain ⟨f₀, hf₀, e, hkey⟩ : ∃ f₀ : S, f₀ ∉ x.asIdeal ∧ ∃ e : S, f₀ * c = a * e := by
    by_cases hax : a ∈ x.asIdeal
    · have hcx' : c ∈ x.asIdeal := hcx hax
      refine ⟨1 - b * c ^ (p - 1), fun hf => ?_, d, ?_⟩
      · apply x.2.ne_top
        rw [Ideal.eq_top_iff_one]
        have hbc : b * c ^ (p - 1) ∈ x.asIdeal :=
          Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hcx' _ (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt))
        have := Ideal.add_mem _ hf hbc
        rwa [sub_add_cancel] at this
      · have hp1 : c ^ (p - 1) * c = c ^ p := by
          rw [← pow_succ, Nat.sub_add_cancel (Fact.out : p.Prime).one_le]
        rw [sub_mul, one_mul, mul_assoc, hp1]
        linear_combination hcrel
    · exact ⟨a, hax, c, rfl⟩

  have hp0 : ((p : ℕ) : Localization.Away f₀) = 0 := by rw [← map_natCast (algebraMap S (Localization.Away f₀)) p, hS, map_zero]
  have hpn0 : IsNilpotent ((p : ℕ) : Localization.Away f₀) := ⟨1, by rw [pow_one, hp0]⟩
  have hc₀ : t.IsGradedS ι ψ ((algebraMap S (Localization.Away f₀)).comp g) :=
    CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent p _ hpn0 _
  have hXm0 : (t.XS g).map (algebraMap S (Localization.Away f₀)) = t.XS ((algebraMap S (Localization.Away f₀)).comp g) := by rw [FormalODModule.map_map]
  have hXr : (t.XS g).F.map (algebraMap S (Localization.Away f₀)) = (t.XS ((algebraMap S (Localization.Away f₀)).comp g)).F := congrArg FormalODModule.F hXm0
  have hj0 : (algebraMap S (Localization.Away f₀)).comp (Rigidified.jS ι ψ g) = Rigidified.jS ι ψ ((algebraMap S (Localization.Away f₀)).comp g) := rfl
  set res : ((t.XS g).toGradedCartierModuleData _ hc).M →+ ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).M := CartierModule.baseChangeEq (p := p) (algebraMap S (Localization.Away f₀)) hXr with hres
  have hresa : IsBaseChangeAlong' (algebraMap S (Localization.Away f₀)) ((t.XS g).toGradedCartierModuleData _ hc) ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀) res := by
    rw [hres]; exact isBaseChangeAlong'_of_eq _ _ _ _ hγS hc _ hXm0 _ hj0 hc₀ hXr
  have hrV := hresa.2.2.1
  have hrPi := hresa.2.2.2.1
  have hγ0_law : (t.XS ((algebraMap S (Localization.Away f₀)).comp g)).IsHomogeneousVBasis (Rigidified.jS ι ψ ((algebraMap S (Localization.Away f₀)).comp g)) (fun i => res (γ i)) :=
    ⟨fun i => hresa.2.2.2.2.1 i _ (hγ.1 i), by rw [hres]; exact isUnit_det_tangent_baseChangeEq _ hXr γ hγS.2⟩
  obtain ⟨hγ0, hD0⟩ := CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData
    p _ (t.XS ((algebraMap S (Localization.Away f₀)).comp g)) _ hγ0_law hc₀
  obtain ⟨L₀, hL₀⟩ := CerednikDrinfeld.FormalODModule.exists_isCanonicalLMap_toGradedCartierModuleData
    p (Rigidified.jS ι ψ ((algebraMap S (Localization.Away f₀)).comp g)) (isHausdorff_of_eq_zero hp0) (t.XS ((algebraMap S (Localization.Away f₀)).comp g)) _ hγ0_law hc₀
  haveI : Nontrivial (Localization.Away f₀) := by
    rw [← not_subsingleton_iff_nontrivial, IsLocalization.subsingleton_iff (M := Submonoid.powers f₀)]
    rintro ⟨n, hn⟩
    have hn' : f₀ ^ n = 0 := hn
    exact hf₀ (x.2.mem_of_pow_mem n (hn' ▸ x.asIdeal.zero_mem))
  haveI : CharP (Localization.Away f₀) p := ringChar.of_eq (CharP.ringChar_of_prime_eq_zero Fact.out hp0)

  have ha' : a ∈ nonZeroDivisors S :=
    mem_nonZeroDivisors_iff.2 ⟨fun s h => ha s h, fun s h => ha s (by rwa [mul_comm] at h)⟩
  have ha0' := IsLocalization.nonZeroDivisors_le_comap (Submonoid.powers f₀) (Localization.Away f₀) ha'
  have ha0 : ∀ s : Localization.Away f₀, (algebraMap S (Localization.Away f₀)) a * s = 0 → s = 0 := (mem_nonZeroDivisors_iff.1 ha0').1
  obtain ⟨u, hu⟩ := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away f₀) f₀
  have hdvd : (algebraMap S (Localization.Away f₀)) a ∣ (algebraMap S (Localization.Away f₀)) c := by
    refine ⟨(algebraMap S (Localization.Away f₀)) e * ↑u⁻¹, ?_⟩
    have h1 : (algebraMap S (Localization.Away f₀)) f₀ * (algebraMap S (Localization.Away f₀)) c = (algebraMap S (Localization.Away f₀)) a * (algebraMap S (Localization.Away f₀)) e := by rw [← map_mul, ← map_mul, hkey]
    rw [← mul_assoc, ← h1, ← hu,
      show (↑u : Localization.Away f₀) * (algebraMap S (Localization.Away f₀)) c * ↑u⁻¹ = (algebraMap S (Localization.Away f₀)) c * (↑u * ↑u⁻¹) by ring,
      Units.mul_inv, mul_one]

  have hnc0 : ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).varpi (res (γ (j + 1 + 1))) =
      WittVector.teichmuller p ((algebraMap S (Localization.Away f₀)) a) • res (γ (j + 1)) + ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).verschiebung (res xj) := by
    rw [fin_two_add_one_add_one, ← hrPi, hnc]
    erw [map_add, hresa.1, WittVector.map_teichmuller, hrV]
  have hcrit0 : ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).varpi (res (γ (j + 1))) = ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).verschiebung (res xj') := by
    rw [← hrPi, hcrit, hrV]
  have hdig0 : res m₀ = WittVector.teichmuller p ((algebraMap S (Localization.Away f₀)) c) • res (γ (j + 1)) + ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).verschiebung (res n) := by
    conv_lhs => rw [hdig]
    erw [map_add, hresa.1, WittVector.map_teichmuller, hrV]
  have hm₀0 : res m₀ ∈ ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).piece (j + 1) := hresa.2.2.2.2.1 _ _ hm₀
  have hinv₀0 : ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).varpi (res m₀) = ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).verschiebung (res m₀) := by
    rw [← hrPi, hinv₀, hrV]

  have hrange := (CerednikDrinfeld.GradedCartierModuleData.exists_eq_varpi_add_verschiebung_iff_dvd_of_varpi_eq_teichmuller_smul_add
      p _ ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀) (fun i => res (γ i)) hγ0 (j + 1) (res xj) ((algebraMap S (Localization.Away f₀)) a) hnc0 ((algebraMap S (Localization.Away f₀)) c) (res n)).2 hdvd
  obtain ⟨xx, hxx, xx', hxeq⟩ := hrange
  rw [fin_two_add_one_add_one] at hxx
  rw [← hdig0] at hxeq

  have hinjL : ∀ m ∈ (t.XS ((algebraMap S (Localization.Away f₀)).comp g)).gradedPiece (Rigidified.jS ι ψ ((algebraMap S (Localization.Away f₀)).comp g)) (j : ℕ),
      (∃ g' : CartierModule p (t.XS ((algebraMap S (Localization.Away f₀)).comp g)).F, verschiebungInt g' = endAct (t.XS ((algebraMap S (Localization.Away f₀)).comp g)).varpiEnd m) →
        ∃ g'' : CartierModule p (t.XS ((algebraMap S (Localization.Away f₀)).comp g)).F, verschiebungInt g'' = m := by
    intro m hm hPi
    obtain ⟨g', hg'⟩ := hPi
    have hg'D : ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).varpi m = ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).verschiebung g' := hg'.symm
    obtain ⟨α, y, hmy⟩ := exists_eq_teichmuller_smul_add_verschiebung ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀) hγ0 j m hm

    have hPim : ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).varpi m =
        WittVector.teichmuller p (α * (algebraMap S (Localization.Away f₀)) a) • res (γ (j + 1)) +
          ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).verschiebung (WittVector.frobenius (WittVector.teichmuller p α) • res xj + ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).varpi y) := by
      have hncj : ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).varpi (res (γ j)) =
          WittVector.teichmuller p ((algebraMap S (Localization.Away f₀)) a) • res (γ (j + 1)) + ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).verschiebung (res xj) := by
        have := hnc0; rwa [fin_two_add_one_add_one] at this
      rw [hmy, map_add, LinearMap.map_smul, hncj, smul_add, smul_smul, ← map_mul, ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).smul_verschiebung,
        ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).varpi_verschiebung, map_add, add_assoc]
    have h0form : ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).verschiebung g' =
        WittVector.teichmuller p (0 : Localization.Away f₀) • res (γ (j + 1)) + ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).verschiebung g' := by
      rw [WittVector.teichmuller_zero, zero_smul, zero_add]
    have hcmp := hPim.symm.trans (hg'D.trans h0form)
    obtain ⟨hα0, -⟩ := digit_unique ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀) hγ0 (j + 1) _ _ _ _ hcmp
    have hα : α = 0 := by
      have := ha0 α (by rw [mul_comm]; exact hα0)
      exact this
    refine ⟨y, ?_⟩
    show ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).verschiebung y = m
    rw [hmy, hα, WittVector.teichmuller_zero, zero_smul, zero_add]
  have hB := CerednikDrinfeld.FormalODModule.bijOn_lambda_etaPiece_of_isCanonicalLMap_of_forall_exists_of_charP
    p (Rigidified.jS ι ψ ((algebraMap S (Localization.Away f₀)).comp g)) (t.XS ((algebraMap S (Localization.Away f₀)).comp g)) hc₀ L₀ hL₀ j hinjL

  have htarget : res m₀ ∈ {m : CartierModule p (t.XS ((algebraMap S (Localization.Away f₀)).comp g)).F |
      m ∈ (t.XS ((algebraMap S (Localization.Away f₀)).comp g)).gradedPiece (Rigidified.jS ι ψ ((algebraMap S (Localization.Away f₀)).comp g)) ((j + 1 : Fin 2) : ℕ) ∧
        endAct (t.XS ((algebraMap S (Localization.Away f₀)).comp g)).varpiEnd m = verschiebungInt m ∧
        ∃ x ∈ (t.XS ((algebraMap S (Localization.Away f₀)).comp g)).gradedPiece (Rigidified.jS ι ψ ((algebraMap S (Localization.Away f₀)).comp g)) (j : ℕ),
          ∃ x' : CartierModule p (t.XS ((algebraMap S (Localization.Away f₀)).comp g)).F, m = endAct (t.XS ((algebraMap S (Localization.Away f₀)).comp g)).varpiEnd x + verschiebungInt x'} :=
    ⟨hm₀0, hinv₀0, xx, hxx, xx', hxeq⟩
  obtain ⟨z₀, hz₀, hlamz₀⟩ := hB.surjOn htarget

  have hLL₀ : ∀ w, L₀ (res w) = ((t.XS g).toGradedCartierModuleData _ hc).nMap ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀) res hrV hrPi (L w) :=
    CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.comp_eq_nMap_comp_of_comp_eq p
      (Rigidified.jS ι ψ g) (Rigidified.jS ι ψ ((algebraMap S (Localization.Away f₀)).comp g)) (algebraMap S (Localization.Away f₀)) hj0 hpS hpn0 ((t.XS g).toGradedCartierModuleData _ hc) hD ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀) hD0 res hresa L hL L₀ hL₀
  have hNz_eta : ((t.XS g).toGradedCartierModuleData _ hc).nMap ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀) res hrV hrPi z ∈ ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).etaPiece L₀ hL₀.isCartierLMap.map_verschiebung j := by
    refine AddSubgroup.mem_inf.2 ⟨?_, ((t.XS g).toGradedCartierModuleData _ hc).R1a_nMap_mem_nPiece ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀) res hrV hrPi hresa.2.2.2.2.1 j z (AddSubgroup.mem_inf.1 hz).2⟩
    rw [mem_eta_iff, ((t.XS g).toGradedCartierModuleData _ hc).R1a_phi_nMap_of_comp ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀) res hrV hrPi hL.isCartierLMap.map_verschiebung
      hL₀.isCartierLMap.map_verschiebung hLL₀, (((t.XS g).toGradedCartierModuleData _ hc).mem_eta_iff _ _ _).1 (AddSubgroup.mem_inf.1 hz).1]
  have hpz₀ : p • z₀ ∈ ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).etaPiece L₀ hL₀.isCartierLMap.map_verschiebung j := AddSubgroup.nsmul_mem _ hz₀ p
  have hlam : ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).lambda (p • z₀) = ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).lambda (((t.XS g).toGradedCartierModuleData _ hc).nMap ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀) res hrV hrPi z) := by
    rw [map_nsmul, ((t.XS g).toGradedCartierModuleData _ hc).R1a_lambda_nMap ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀) res hrV hrPi, ← hpm₀, map_nsmul]
    exact congrArg _ hlamz₀
  refine ⟨f₀, hf₀, hc₀, L₀, hL₀, hXr, ?_, ?_, z₀, hz₀, ?_⟩
  · intro w; exact hrV w
  · intro w; exact hrPi w
  · exact hB.injOn hpz₀ hNz_eta hlam

end S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_smul_eq_nMap_of_nsmul_eq_lambda_of_varpi_eq_teichmuller_smul_add_verschiebung
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_smul_eq_nMap_of_nsmul_eq_lambda_of_varpi_eq_teichmuller_smul_add_verschiebung (solution)
