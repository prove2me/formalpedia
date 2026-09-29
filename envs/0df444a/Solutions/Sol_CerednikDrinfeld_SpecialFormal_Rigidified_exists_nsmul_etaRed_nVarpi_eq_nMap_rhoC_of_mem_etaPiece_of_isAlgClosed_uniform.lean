-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.exists_nsmul_etaRed_nVarpi_eq_nMap_rhoC_of_mem_etaPiece_of_isAlgClosed_uniform
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/68ad3a3e-e1b9-5800-bf66-83d808c1bb95

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_CartierQuadrupleVia
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_rhoC_eq_nsmul_and_rhoC_injective_of_isAlgClosed
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_isCompl_nPiece_zero_one
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_IsCanonicalLMap_exists_mem_etaPiece_add_eq
import Theorems.Thm_CerednikDrinfeld_FormalODModule_IsODHom_map_mem_gradedPiece
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_IsCanonicalLMap_comp_eq_nMap_comp_of_isNilpotent
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isCanonicalLMap_toGradedCartierModuleData
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isBaseChangeAlong_toGradedCartierModuleData_baseChange
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isHomogeneousVBasis_of_isHomogeneousVBasis_toGradedCartierModuleData
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isSpecialCartierModule_toGradedCartierModuleData
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_nsmul_etaRed_nVarpi_eq_nMap_rhoC_of_mem_etaPiece_of_isAlgClosed_uniform
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply"

set_option autoImplicit false

p2m_open "CerednikDrinfeld P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_nsmul_etaRed_nVarpi_eq_nMap_rhoC_of_mem_etaPiece_of_isAlgClosed_uniform.CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega"

open scoped PadicInt Padic

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "Zp2 FormalODModule FormalODModule.map_map FormalODModule.IsODHom SpecialFormal.Rigidified GradedCartierModuleData GradedCartierModuleData.IsCanonicalLMap FormalODModule.mem_toGradedCartierModuleData_piece_iff SpecialFormal.Rigidified.exists_rhoC_eq_nsmul_and_rhoC_injective_of_isAlgClosed GradedCartierModuleData.isCompl_nPiece_zero_one GradedCartierModuleData.IsCanonicalLMap.exists_mem_etaPiece_add_eq FormalODModule.IsODHom.map_mem_gradedPiece GradedCartierModuleData.IsCanonicalLMap.comp_eq_nMap_comp_of_isNilpotent FormalODModule.exists_isCanonicalLMap_toGradedCartierModuleData FormalODModule.isBaseChangeAlong_toGradedCartierModuleData_baseChange FormalODModule.isHomogeneousVBasis_of_isHomogeneousVBasis_toGradedCartierModuleData FormalODModule.isSpecialCartierModule_toGradedCartierModuleData"
namespace GradedCartierModuleData
p2m_export "CerednikDrinfeld.GradedCartierModuleData" "IsHomogeneousVBasis IsSpecialCartierModule varpi_varpi varpi module mk M frobenius piece verschiebung varpi_mem varpi_verschiebung varpi_frobenius NMod nMk nMk_surjective nMk_verschiebung_neg_varpi lambda lambda_nMk nVarpi nPiece nMap nMap_nMk IsBaseChangeAlong' IsCartierLMap IsCanonicalLMap phi phi_nMk eta mem_eta_iff etaPiece isCompl_nPiece_zero_one IsCanonicalLMap.exists_mem_etaPiece_add_eq IsCanonicalLMap.comp_eq_nMap_comp_of_isNilpotent"
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

theorem R1a_lambda_nMap (D : GradedCartierModuleData p B j) (D' : GradedCartierModuleData p B' j')
    (f : D.M →+ D'.M) (hV : ∀ x, f (D.verschiebung x) = D'.verschiebung (f x))
    (hPi : ∀ x, f (D.varpi x) = D'.varpi (f x)) (z : D.NMod) :
    D'.lambda (D.nMap D' f hV hPi z) = f (D.lambda z) := by
  obtain ⟨⟨a, b⟩, rfl⟩ := D.nMk_surjective z
  rw [nMap_nMk, lambda_nMk, lambda_nMk, map_add, hPi, hV]

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

private theorem _root_.CerednikDrinfeld.GradedCartierModuleData.R1a_nsmul_nVarpi_mem_etaPiece (D : GradedCartierModuleData p B j) {L : D.M →+ D.NMod}
    (hL : D.IsCartierLMap L) {i : Fin 2} {z : D.NMod} (hz : z ∈ D.etaPiece L hL.map_verschiebung i) :
    (p : ℕ) • D.nVarpi z ∈ D.etaPiece L hL.map_verschiebung (i + 1) := by
  obtain ⟨hz1, hz2⟩ := AddSubgroup.mem_inf.1 hz
  refine AddSubgroup.mem_inf.2 ⟨?_, AddSubgroup.nsmul_mem _ (D.R1a_nVarpi_mem_nPiece hz2) _⟩
  rw [mem_eta_iff] at hz1 ⊢
  rw [map_nsmul, R1a_nsmul_phi_nVarpi D hL, hz1]

p2m_export "CerednikDrinfeld.GradedCartierModuleData" "R1a_nsmul_nVarpi_mem_etaPiece"

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

private theorem _root_.CerednikDrinfeld.GradedCartierModuleData.R1a_phi_nsmul_eq_of_phi_nMap_eq (D : GradedCartierModuleData p B j) (D' : GradedCartierModuleData p B' j')
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

p2m_export "CerednikDrinfeld.GradedCartierModuleData" "R1a_phi_nsmul_eq_of_phi_nMap_eq"

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

p2m_open "MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_nsmul_etaRed_nVarpi_eq_nMap_rhoC_of_mem_etaPiece_of_isAlgClosed_uniform.CerednikDrinfeld CerednikDrinfeld.GradedCartierModuleData P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_nsmul_etaRed_nVarpi_eq_nMap_rhoC_of_mem_etaPiece_of_isAlgClosed_uniform.CerednikDrinfeld.GradedCartierModuleData CerednikDrinfeld.SpecialFormal CerednikDrinfeld.SpecialFormal.Rigidified"

namespace R1aUAux

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

omit [Fact p.Prime] in
theorem isHausdorff_of_isNilpotent {S : Type} [CommRing S] (hS : IsNilpotent ((p : ℕ) : S)) :
    IsHausdorff (Ideal.span {((p : ℕ) : S)}) S := by
  obtain ⟨N, hN⟩ := hS
  refine ⟨fun x hx => ?_⟩
  have := hx N
  rwa [Ideal.span_singleton_pow, hN, Ideal.span_singleton_eq_bot.mpr rfl, Submodule.bot_smul, SModEq.bot] at this

end R1aUAux

open R1aUAux

theorem solution
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι)) (hΦ4 : Φ.HasHeight 4)
    (h0Φ : Φ.lieZero ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) ≤ LinearMap.ker Φ.lieVarpi)
    (hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0) (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
    (hrΦ : ∀ (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
      (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L),
      Set.BijOn rΦ Set.univ ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung 0 : Set _))
    (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [Algebra ℤ_[p] K] (ψ' : WittVector p k →+* K) (hK : IsNilpotent (p : K))
    (t' : Rigidified p Φ K) (ht' : t'.IsAdmissible ι ψ')
    (hc : t'.IsGradedS ι ψ' (Rigidified.awayHom (1 : K))) (hcb : t'.IsGradedSbar ι ψ' (Rigidified.awayHom (1 : K)))
    (hcΦ1 : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ' (Rigidified.awayHom (1 : K)))
    (L' : ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).M →+
      ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).NMod)
    (hL' : ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).IsCanonicalLMap L') :
    ∀ (LΦ : ((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).M →+ ((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).NMod) (hLΦ : ((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).IsCanonicalLMap LΦ), ∃ N : ℕ,
      ∀ (i : Fin 2) (z : ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).NMod), z ∈ ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).etaPiece L' hL'.isCartierLMap.map_verschiebung i →
      ∃ x : ((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).NMod, x ∈ ((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).etaPiece LΦ hLΦ.isCartierLMap.map_verschiebung 0 ∧
        p ^ N • t'.etaRed ι ψ' (Rigidified.awayHom (1 : K)) hc hcb (((((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).nVarpi : ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).NMod →ₗ[WittVector p (Rigidified.Baway (1 : K))] ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).NMod) ^ (i : ℕ)) z) = ((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).nMap ((t'.XbarS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jSbar ι ψ' (Rigidified.awayHom (1 : K))) hcb) (Rigidified.rhoC ψ' t' ht'.2.2.1.1 (Rigidified.awayHom (1 : K))) (Rigidified.rhoC_verschiebungInt ψ' t' ht'.2.2.1.1 (Rigidified.awayHom (1 : K))) (Rigidified.rhoC_endAct_varpiEnd ψ' t' ht'.2.2.1 (Rigidified.awayHom (1 : K))) x := by
  intro LΦ hLΦ
  classical

  obtain ⟨⟨h, hcof⟩, hinj⟩ :=
    CerednikDrinfeld.SpecialFormal.Rigidified.exists_rhoC_eq_nsmul_and_rhoC_injective_of_isAlgClosed
      p k ι Φ hΦ hΦ4 h0Φ hcΦ rΦ hrΦ K ψ' hK t' ht' hc hcb hcΦ1 L' hL'
  refine ⟨h + 3, ?_⟩
  intro i z hz
  have hS : IsNilpotent ((p : ℕ) : Rigidified.Baway (1 : K)) := by
    obtain ⟨n, hn⟩ := hK
    exact ⟨n, by rw [← map_natCast (Rigidified.awayHom (1 : K)) p, ← map_pow, hn, map_zero]⟩
  have hp0 : IsNilpotent ((p : ℕ) : Rigidified.Baway (1 : K) ⧸ pIdeal p (Rigidified.Baway (1 : K))) :=
    ⟨1, by rw [pow_one]; exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))⟩

  have hmk : (Ideal.Quotient.mk (pIdeal p (Rigidified.Baway (1 : K)))).comp (Rigidified.awayHom (1 : K)) =
      (reduceMap (p := p) (Rigidified.awayHom (1 : K))).comp (Ideal.Quotient.mk (pIdeal p K)) := by
    ext b; rfl
  have hXm : (t'.XS (Rigidified.awayHom (1 : K))).map (Ideal.Quotient.mk (pIdeal p (Rigidified.Baway (1 : K)))) = t'.XbarS (Rigidified.awayHom (1 : K)) := by
    show (t'.X.map (Rigidified.awayHom (1 : K))).map (Ideal.Quotient.mk (pIdeal p (Rigidified.Baway (1 : K)))) =
      (t'.X.map (Ideal.Quotient.mk (pIdeal p K))).map (reduceMap (p := p) (Rigidified.awayHom (1 : K)))
    rw [FormalODModule.map_map, FormalODModule.map_map, hmk]
  have hjb : (Ideal.Quotient.mk (pIdeal p (Rigidified.Baway (1 : K)))).comp (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) =
      Rigidified.jSbar ι ψ' (Rigidified.awayHom (1 : K)) := by
    show (Ideal.Quotient.mk (pIdeal p (Rigidified.Baway (1 : K)))).comp ((Rigidified.awayHom (1 : K)).comp (structureMap ι ψ')) =
      (reduceMap (p := p) (Rigidified.awayHom (1 : K))).comp ((Ideal.Quotient.mk (pIdeal p K)).comp (structureMap ι ψ'))
    rw [← RingHom.comp_assoc, hmk, RingHom.comp_assoc]
  have hF : (t'.XS (Rigidified.awayHom (1 : K))).F.map (Ideal.Quotient.mk (pIdeal p (Rigidified.Baway (1 : K)))) = (t'.XbarS (Rigidified.awayHom (1 : K))).F :=
    t'.XS_F_map_mk (Rigidified.awayHom (1 : K))

  obtain ⟨Sl, _, jl, φl, _, _, Dl, _, fl, hfl, Ll, _, _⟩ := hL'.exists_lift
  obtain ⟨γl, _, hγf⟩ := hfl.2.2.2.2.2
  have hγ : (t'.XS (Rigidified.awayHom (1 : K))).IsHomogeneousVBasis (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) (fun i => fl (γl i)) :=
    CerednikDrinfeld.FormalODModule.isHomogeneousVBasis_of_isHomogeneousVBasis_toGradedCartierModuleData p _ _ hc _ hγf
  have hbca : IsBaseChangeAlong' (Ideal.Quotient.mk (pIdeal p (Rigidified.Baway (1 : K)))) ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc) ((t'.XbarS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jSbar ι ψ' (Rigidified.awayHom (1 : K))) hcb)
      (CartierModule.baseChangeEq (Ideal.Quotient.mk (pIdeal p (Rigidified.Baway (1 : K)))) hF) :=
    isBaseChangeAlong'_of_eq _ _ _ _ hγ hc _ hXm _ hjb hcb hF
  have hγb : (t'.XbarS (Rigidified.awayHom (1 : K))).IsHomogeneousVBasis (Rigidified.jSbar ι ψ' (Rigidified.awayHom (1 : K)))
      (fun i => CartierModule.baseChangeEq (Ideal.Quotient.mk (pIdeal p (Rigidified.Baway (1 : K)))) hF (fl (γl i))) := by
    refine ⟨fun i => ?_, isUnit_det_tangent_baseChangeEq _ hF _ hγ.2⟩
    exact (FormalODModule.mem_toGradedCartierModuleData_piece_iff _ _ hcb i _).mp
      (hbca.2.2.2.2.1 i _ ((FormalODModule.mem_toGradedCartierModuleData_piece_iff _ _ hc i _).mpr (hγ.1 i)))
  obtain ⟨Lb, hLb⟩ := CerednikDrinfeld.FormalODModule.exists_isCanonicalLMap_toGradedCartierModuleData p
    (Rigidified.jSbar ι ψ' (Rigidified.awayHom (1 : K))) (isHausdorff_of_isNilpotent hp0) _ _ hγb hcb
  have hD : ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).IsSpecialCartierModule :=
    (CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData p _ _ _ hγ hc).2
  have hDb : ((t'.XbarS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jSbar ι ψ' (Rigidified.awayHom (1 : K))) hcb).IsSpecialCartierModule :=
    (CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData p _ _ _ hγb hcb).2
  have hLLb : ∀ x, Lb (CartierModule.baseChangeEq (Ideal.Quotient.mk (pIdeal p (Rigidified.Baway (1 : K)))) hF x) =
      ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).nMap ((t'.XbarS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jSbar ι ψ' (Rigidified.awayHom (1 : K))) hcb) (CartierModule.baseChangeEq (Ideal.Quotient.mk (pIdeal p (Rigidified.Baway (1 : K)))) hF) hbca.2.2.1 hbca.2.2.2.1 (L' x) :=
    natL_of_eq _ (Ideal.Quotient.mk (pIdeal p (Rigidified.Baway (1 : K)))) hS hp0 ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc) hD _ hjb ((t'.XbarS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jSbar ι ψ' (Rigidified.awayHom (1 : K))) hcb) hDb _ hbca L' hL' Lb hLb

  have hw0 : (p : ℕ) • ((((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).nVarpi : ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).NMod →ₗ[WittVector p (Rigidified.Baway (1 : K))] ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).NMod) ^ (i : ℕ)) z ∈
      ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).etaPiece L' hL'.isCartierLMap.map_verschiebung 0 := by
    have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    rcases hi with rfl | rfl
    · simpa using AddSubgroup.nsmul_mem _ hz p
    · have := ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).R1a_nsmul_nVarpi_mem_etaPiece hL'.isCartierLMap hz
      simpa using this

  have hred_def : t'.etaRed ι ψ' (Rigidified.awayHom (1 : K)) hc hcb = (((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).nMap ((t'.XbarS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jSbar ι ψ' (Rigidified.awayHom (1 : K))) hcb) (t'.redC (Rigidified.awayHom (1 : K))) (t'.redC_verschiebungInt (Rigidified.awayHom (1 : K))) (t'.redC_endAct_varpiEnd (Rigidified.awayHom (1 : K)))) := rfl
  have hy_fix : ((t'.XbarS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jSbar ι ψ' (Rigidified.awayHom (1 : K))) hcb).phi Lb hLb.isCartierLMap.map_verschiebung
      ((((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).nMap ((t'.XbarS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jSbar ι ψ' (Rigidified.awayHom (1 : K))) hcb) (t'.redC (Rigidified.awayHom (1 : K))) (t'.redC_verschiebungInt (Rigidified.awayHom (1 : K))) (t'.redC_endAct_varpiEnd (Rigidified.awayHom (1 : K)))) ((p : ℕ) • ((((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).nVarpi : ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).NMod →ₗ[WittVector p (Rigidified.Baway (1 : K))] ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).NMod) ^ (i : ℕ)) z)) =
      (((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).nMap ((t'.XbarS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jSbar ι ψ' (Rigidified.awayHom (1 : K))) hcb) (t'.redC (Rigidified.awayHom (1 : K))) (t'.redC_verschiebungInt (Rigidified.awayHom (1 : K))) (t'.redC_endAct_varpiEnd (Rigidified.awayHom (1 : K)))) ((p : ℕ) • ((((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).nVarpi : ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).NMod →ₗ[WittVector p (Rigidified.Baway (1 : K))] ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).NMod) ^ (i : ℕ)) z) := by
    rw [((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).R1a_phi_nMap_of_comp ((t'.XbarS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jSbar ι ψ' (Rigidified.awayHom (1 : K))) hcb) _ hbca.2.2.1 hbca.2.2.2.1 hL'.isCartierLMap.map_verschiebung
      hLb.isCartierLMap.map_verschiebung hLLb]
    congr 1
    exact (((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).mem_eta_iff _ _ _).1 (AddSubgroup.mem_inf.1 hw0).1
  have hy_piece : (((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).nMap ((t'.XbarS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jSbar ι ψ' (Rigidified.awayHom (1 : K))) hcb) (t'.redC (Rigidified.awayHom (1 : K))) (t'.redC_verschiebungInt (Rigidified.awayHom (1 : K))) (t'.redC_endAct_varpiEnd (Rigidified.awayHom (1 : K)))) ((p : ℕ) • ((((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).nVarpi : ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).NMod →ₗ[WittVector p (Rigidified.Baway (1 : K))] ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).NMod) ^ (i : ℕ)) z) ∈ ((t'.XbarS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jSbar ι ψ' (Rigidified.awayHom (1 : K))) hcb).nPiece 0 :=
    ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).R1a_nMap_mem_nPiece ((t'.XbarS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jSbar ι ψ' (Rigidified.awayHom (1 : K))) hcb) _ _ _ hbca.2.2.2.2.1 0 _ (AddSubgroup.mem_inf.1 hw0).2

  have hcofN : ∀ w : ((t'.XbarS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jSbar ι ψ' (Rigidified.awayHom (1 : K))) hcb).NMod, ∃ w₀ : ((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).NMod, (((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).nMap ((t'.XbarS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jSbar ι ψ' (Rigidified.awayHom (1 : K))) hcb) (Rigidified.rhoC ψ' t' ht'.2.2.1.1 (Rigidified.awayHom (1 : K))) (Rigidified.rhoC_verschiebungInt ψ' t' ht'.2.2.1.1 (Rigidified.awayHom (1 : K))) (Rigidified.rhoC_endAct_varpiEnd ψ' t' ht'.2.2.1 (Rigidified.awayHom (1 : K)))) w₀ = (p ^ h : ℕ) • w := by
    intro w
    obtain ⟨⟨m₁, m₂⟩, rfl⟩ := ((t'.XbarS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jSbar ι ψ' (Rigidified.awayHom (1 : K))) hcb).nMk_surjective w
    obtain ⟨a₁, h₁⟩ := hcof m₁
    obtain ⟨a₂, h₂⟩ := hcof m₂
    refine ⟨((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).nMk (a₁, a₂), ?_⟩
    rw [nMap_nMk, ← map_nsmul, Prod.smul_mk]
    exact congrArg _ (Prod.ext h₁ h₂)
  obtain ⟨x₀, hx₀⟩ := hcofN ((((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).nMap ((t'.XbarS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jSbar ι ψ' (Rigidified.awayHom (1 : K))) hcb) (t'.redC (Rigidified.awayHom (1 : K))) (t'.redC_verschiebungInt (Rigidified.awayHom (1 : K))) (t'.redC_endAct_varpiEnd (Rigidified.awayHom (1 : K)))) ((p : ℕ) • ((((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).nVarpi : ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).NMod →ₗ[WittVector p (Rigidified.Baway (1 : K))] ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).NMod) ^ (i : ℕ)) z))

  have hrF : ∀ x, (Rigidified.rhoC ψ' t' ht'.2.2.1.1 (Rigidified.awayHom (1 : K))) (((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).frobenius x) = ((t'.XbarS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jSbar ι ψ' (Rigidified.awayHom (1 : K))) hcb).frobenius ((Rigidified.rhoC ψ' t' ht'.2.2.1.1 (Rigidified.awayHom (1 : K))) x) := fun x =>
    CartierModule.map_frobenius _ x
  have hx1 : ((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).phi LΦ hLΦ.isCartierLMap.map_verschiebung ((p ^ 2 : ℕ) • x₀) = (p ^ 2 : ℕ) • x₀ := by
    refine ((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).R1a_phi_nsmul_eq_of_phi_nMap_eq ((t'.XbarS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jSbar ι ψ' (Rigidified.awayHom (1 : K))) hcb) (Rigidified.rhoC ψ' t' ht'.2.2.1.1 (Rigidified.awayHom (1 : K))) hrF
      (Rigidified.rhoC_verschiebungInt ψ' t' ht'.2.2.1.1 (Rigidified.awayHom (1 : K))) (Rigidified.rhoC_endAct_varpiEnd ψ' t' ht'.2.2.1 (Rigidified.awayHom (1 : K)))
      hinj hLΦ.isCartierLMap hLb.isCartierLMap x₀ ?_
    rw [hx₀, map_nsmul, hy_fix]
  have hx1_eta : (p ^ 2 : ℕ) • x₀ ∈ ((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).eta LΦ hLΦ.isCartierLMap.map_verschiebung :=
    (((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).mem_eta_iff _ _ _).2 hx1

  obtain ⟨x0, hx0, x1, hx1m, hxx⟩ :=
    CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.exists_mem_etaPiece_add_eq p _ ((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1) LΦ hLΦ _ hx1_eta
  have hjj : Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K)) = Rigidified.jSbar ι ψ' (Rigidified.awayHom (1 : K)) := RingHom.ext fun x => rfl
  have hrpc : ∀ (n : Fin 2) (x : CartierModule p (Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).F), x ∈ ((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).piece n →
      (Rigidified.rhoC ψ' t' ht'.2.2.1.1 (Rigidified.awayHom (1 : K))) x ∈ ((t'.XbarS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jSbar ι ψ' (Rigidified.awayHom (1 : K))) hcb).piece n := by
    intro n x hx
    have hx' := (FormalODModule.mem_toGradedCartierModuleData_piece_iff _ _ hcΦ1 n _).mp hx
    have h3 := CerednikDrinfeld.FormalODModule.IsODHom.map_mem_gradedPiece p (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K)))
      (Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))) (t'.XbarS (Rigidified.awayHom (1 : K))) _ (ht'.2.2.1.map (reduceMap (p := p) (Rigidified.awayHom (1 : K)))) n _ hx'
    rw [hjj] at h3
    exact (FormalODModule.mem_toGradedCartierModuleData_piece_iff _ _ hcb n _).mpr h3
  have h1piece : (((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).nMap ((t'.XbarS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jSbar ι ψ' (Rigidified.awayHom (1 : K))) hcb) (Rigidified.rhoC ψ' t' ht'.2.2.1.1 (Rigidified.awayHom (1 : K))) (Rigidified.rhoC_verschiebungInt ψ' t' ht'.2.2.1.1 (Rigidified.awayHom (1 : K))) (Rigidified.rhoC_endAct_varpiEnd ψ' t' ht'.2.2.1 (Rigidified.awayHom (1 : K)))) x1 ∈ ((t'.XbarS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jSbar ι ψ' (Rigidified.awayHom (1 : K))) hcb).nPiece 1 :=
    ((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).R1a_nMap_mem_nPiece ((t'.XbarS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jSbar ι ψ' (Rigidified.awayHom (1 : K))) hcb) _ _ _ hrpc 1 _ (AddSubgroup.mem_inf.1 hx1m).2
  have h0piece : (((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).nMap ((t'.XbarS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jSbar ι ψ' (Rigidified.awayHom (1 : K))) hcb) (Rigidified.rhoC ψ' t' ht'.2.2.1.1 (Rigidified.awayHom (1 : K))) (Rigidified.rhoC_verschiebungInt ψ' t' ht'.2.2.1.1 (Rigidified.awayHom (1 : K))) (Rigidified.rhoC_endAct_varpiEnd ψ' t' ht'.2.2.1 (Rigidified.awayHom (1 : K)))) x0 ∈ ((t'.XbarS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jSbar ι ψ' (Rigidified.awayHom (1 : K))) hcb).nPiece 0 :=
    ((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).R1a_nMap_mem_nPiece ((t'.XbarS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jSbar ι ψ' (Rigidified.awayHom (1 : K))) hcb) _ _ _ hrpc 0 _ (AddSubgroup.mem_inf.1 hx0).2
  have hsum : (((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).nMap ((t'.XbarS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jSbar ι ψ' (Rigidified.awayHom (1 : K))) hcb) (Rigidified.rhoC ψ' t' ht'.2.2.1.1 (Rigidified.awayHom (1 : K))) (Rigidified.rhoC_verschiebungInt ψ' t' ht'.2.2.1.1 (Rigidified.awayHom (1 : K))) (Rigidified.rhoC_endAct_varpiEnd ψ' t' ht'.2.2.1 (Rigidified.awayHom (1 : K)))) x0 + (((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).nMap ((t'.XbarS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jSbar ι ψ' (Rigidified.awayHom (1 : K))) hcb) (Rigidified.rhoC ψ' t' ht'.2.2.1.1 (Rigidified.awayHom (1 : K))) (Rigidified.rhoC_verschiebungInt ψ' t' ht'.2.2.1.1 (Rigidified.awayHom (1 : K))) (Rigidified.rhoC_endAct_varpiEnd ψ' t' ht'.2.2.1 (Rigidified.awayHom (1 : K)))) x1 =
      (p ^ 2 : ℕ) • ((p ^ h : ℕ) • (((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).nMap ((t'.XbarS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jSbar ι ψ' (Rigidified.awayHom (1 : K))) hcb) (t'.redC (Rigidified.awayHom (1 : K))) (t'.redC_verschiebungInt (Rigidified.awayHom (1 : K))) (t'.redC_endAct_varpiEnd (Rigidified.awayHom (1 : K)))) ((p : ℕ) • ((((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).nVarpi : ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).NMod →ₗ[WittVector p (Rigidified.Baway (1 : K))] ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).NMod) ^ (i : ℕ)) z)) := by
    rw [← map_add, ← hxx, map_nsmul, hx₀]
  have h1zero : (((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).nMap ((t'.XbarS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jSbar ι ψ' (Rigidified.awayHom (1 : K))) hcb) (Rigidified.rhoC ψ' t' ht'.2.2.1.1 (Rigidified.awayHom (1 : K))) (Rigidified.rhoC_verschiebungInt ψ' t' ht'.2.2.1.1 (Rigidified.awayHom (1 : K))) (Rigidified.rhoC_endAct_varpiEnd ψ' t' ht'.2.2.1 (Rigidified.awayHom (1 : K)))) x1 = 0 := by
    have h1' : (((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).nMap ((t'.XbarS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jSbar ι ψ' (Rigidified.awayHom (1 : K))) hcb) (Rigidified.rhoC ψ' t' ht'.2.2.1.1 (Rigidified.awayHom (1 : K))) (Rigidified.rhoC_verschiebungInt ψ' t' ht'.2.2.1.1 (Rigidified.awayHom (1 : K))) (Rigidified.rhoC_endAct_varpiEnd ψ' t' ht'.2.2.1 (Rigidified.awayHom (1 : K)))) x1 ∈ ((t'.XbarS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jSbar ι ψ' (Rigidified.awayHom (1 : K))) hcb).nPiece 0 := by
      have : (((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).nMap ((t'.XbarS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jSbar ι ψ' (Rigidified.awayHom (1 : K))) hcb) (Rigidified.rhoC ψ' t' ht'.2.2.1.1 (Rigidified.awayHom (1 : K))) (Rigidified.rhoC_verschiebungInt ψ' t' ht'.2.2.1.1 (Rigidified.awayHom (1 : K))) (Rigidified.rhoC_endAct_varpiEnd ψ' t' ht'.2.2.1 (Rigidified.awayHom (1 : K)))) x1 = (p ^ 2 : ℕ) • ((p ^ h : ℕ) • (((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).nMap ((t'.XbarS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jSbar ι ψ' (Rigidified.awayHom (1 : K))) hcb) (t'.redC (Rigidified.awayHom (1 : K))) (t'.redC_verschiebungInt (Rigidified.awayHom (1 : K))) (t'.redC_endAct_varpiEnd (Rigidified.awayHom (1 : K)))) ((p : ℕ) • ((((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).nVarpi : ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).NMod →ₗ[WittVector p (Rigidified.Baway (1 : K))] ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).NMod) ^ (i : ℕ)) z)) - (((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).nMap ((t'.XbarS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jSbar ι ψ' (Rigidified.awayHom (1 : K))) hcb) (Rigidified.rhoC ψ' t' ht'.2.2.1.1 (Rigidified.awayHom (1 : K))) (Rigidified.rhoC_verschiebungInt ψ' t' ht'.2.2.1.1 (Rigidified.awayHom (1 : K))) (Rigidified.rhoC_endAct_varpiEnd ψ' t' ht'.2.2.1 (Rigidified.awayHom (1 : K)))) x0 := by
        rw [← hsum]; abel
      rw [this]
      exact AddSubgroup.sub_mem _ (AddSubgroup.nsmul_mem _ (AddSubgroup.nsmul_mem _ hy_piece _) _) h0piece
    have hNb := CerednikDrinfeld.GradedCartierModuleData.isCompl_nPiece_zero_one p _ ((t'.XbarS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jSbar ι ψ' (Rigidified.awayHom (1 : K))) hcb)
    have := AddSubgroup.mem_inf.mpr ⟨h1', h1piece⟩
    rwa [hNb.inf_eq_bot, AddSubgroup.mem_bot] at this

  refine ⟨x0, hx0, ?_⟩
  rw [hred_def]
  have hfin : (((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).nMap ((t'.XbarS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jSbar ι ψ' (Rigidified.awayHom (1 : K))) hcb) (Rigidified.rhoC ψ' t' ht'.2.2.1.1 (Rigidified.awayHom (1 : K))) (Rigidified.rhoC_verschiebungInt ψ' t' ht'.2.2.1.1 (Rigidified.awayHom (1 : K))) (Rigidified.rhoC_endAct_varpiEnd ψ' t' ht'.2.2.1 (Rigidified.awayHom (1 : K)))) x0 = (p ^ 2 : ℕ) • ((p ^ h : ℕ) • (((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).nMap ((t'.XbarS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jSbar ι ψ' (Rigidified.awayHom (1 : K))) hcb) (t'.redC (Rigidified.awayHom (1 : K))) (t'.redC_verschiebungInt (Rigidified.awayHom (1 : K))) (t'.redC_endAct_varpiEnd (Rigidified.awayHom (1 : K)))) ((p : ℕ) • ((((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).nVarpi : ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).NMod →ₗ[WittVector p (Rigidified.Baway (1 : K))] ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).NMod) ^ (i : ℕ)) z)) := by
    rw [← hsum, h1zero, add_zero]
  rw [hfin, map_nsmul, smul_smul, smul_smul, ← pow_add, ← pow_succ]
  congr 1
  ring

end S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_nsmul_etaRed_nVarpi_eq_nMap_rhoC_of_mem_etaPiece_of_isAlgClosed_uniform
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_nsmul_etaRed_nVarpi_eq_nMap_rhoC_of_mem_etaPiece_of_isAlgClosed_uniform (solution)
