-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.nMap_bcPhi_rPhi_injective_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/30190d46-97a6-5aaa-ba49-d5c4f87ccb93

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
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isCanonicalLMap_toGradedCartierModuleData_of_isSpecial_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_nMap_bcPhi_rPhi_injective_of_isAlgClosed
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt"

set_option autoImplicit false

p2m_open "CerednikDrinfeld P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_nMap_bcPhi_rPhi_injective_of_isAlgClosed.CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega"

open scoped PadicInt Padic

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "Zp2 FormalODModule GradedCartierModuleData FormalODModule.exists_isCanonicalLMap_toGradedCartierModuleData_of_isSpecial_of_isAlgClosed"
namespace GradedCartierModuleData
p2m_export "CerednikDrinfeld.GradedCartierModuleData" "varpi_varpi varpi mk M frobenius piece verschiebung varpi_mem varpi_verschiebung varpi_frobenius NMod nMk nMk_surjective nMk_verschiebung_neg_varpi lambda lambda_nMk nVarpi nPiece nMap nMap_nMk IsCartierLMap IsCanonicalLMap phi phi_nMk mem_eta_iff etaPiece u"
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

private theorem _root_.CerednikDrinfeld.GradedCartierModuleData.R1a_nsmul_eq_zero_of_nMap_eq_zero (D : GradedCartierModuleData p B j) (D' : GradedCartierModuleData p B' j')
    (f : D.M →+ D'.M) (hV : ∀ x, f (D.verschiebung x) = D'.verschiebung (f x))
    (hPi : ∀ x, f (D.varpi x) = D'.varpi (f x)) (hf : Function.Injective f)
    (z : D.NMod) (hz : D.nMap D' f hV hPi z = 0) : (p : ℕ) • z = 0 := by
  apply R1a_nsmul_eq_zero_of_lambda_eq_zero
  apply hf
  rw [← R1a_lambda_nMap D D' f hV hPi, hz, map_zero, map_zero]

p2m_export "CerednikDrinfeld.GradedCartierModuleData" "R1a_nsmul_eq_zero_of_nMap_eq_zero"
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
theorem R1a_nMap_mem_nPiece (D : GradedCartierModuleData p B j) (D' : GradedCartierModuleData p B' j')
    (f : D.M →+ D'.M) (hV : ∀ x, f (D.verschiebung x) = D'.verschiebung (f x))
    (hPi : ∀ x, f (D.varpi x) = D'.varpi (f x))
    (hpc : ∀ (i : Fin 2) (x : D.M), x ∈ D.piece i → f x ∈ D'.piece i)
    (m : Fin 2) (n : D.NMod) (hn : n ∈ D.nPiece m) : D.nMap D' f hV hPi n ∈ D'.nPiece m := by
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := AddSubgroup.mem_map.mp hn
  obtain ⟨ha, hb⟩ := AddSubgroup.mem_prod.mp hab
  rw [nMap_nMk]
  exact AddSubgroup.mem_map.mpr ⟨(f a, f b), AddSubgroup.mem_prod.mpr ⟨hpc m a ha, hpc m b hb⟩, rfl⟩

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

theorem R1a_phi_nMap_of_comp (D : GradedCartierModuleData p B j) (D' : GradedCartierModuleData p B' j')
    (f : D.M →+ D'.M) (hV : ∀ x, f (D.verschiebung x) = D'.verschiebung (f x))
    (hPi : ∀ x, f (D.varpi x) = D'.varpi (f x))
    {L : D.M →+ D.NMod} (hL : ∀ x, L (D.verschiebung x) = D.nMk (D.varpi x, 0))
    {L' : D'.M →+ D'.NMod} (hL' : ∀ x, L' (D'.verschiebung x) = D'.nMk (D'.varpi x, 0))
    (hLL : ∀ x, L' (f x) = D.nMap D' f hV hPi (L x)) (w : D.NMod) :
    D'.phi L' hL' (D.nMap D' f hV hPi w) = D.nMap D' f hV hPi (D.phi L hL w) := by
  obtain ⟨⟨x, x'⟩, rfl⟩ := D.nMk_surjective w
  rw [nMap_nMk, phi_nMk, phi_nMk, map_add, nMap_nMk, hLL, map_zero]

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
    Function.Injective (fun w : Fin 2 → ℤ_[p] => (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMap ((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1) (Rigidified.bcPhi (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))) (Rigidified.bcPhi_verschiebungInt (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))) (Rigidified.bcPhi_endAct_varpiEnd (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))) (rΦ w)) := by

  obtain ⟨LΦ0, hLΦ0⟩ :=
    CerednikDrinfeld.FormalODModule.exists_isCanonicalLMap_toGradedCartierModuleData_of_isSpecial_of_isAlgClosed
      p k ι Φ hΦ hcΦ
  have hinjr : Function.Injective rΦ := Set.injOn_univ.1 (hrΦ LΦ0 hLΦ0).injOn

  have hpK : pIdeal p K = ⊥ := Ideal.span_singleton_eq_bot.mpr (CharP.cast_eq_zero K p)
  have hS1 : Function.Injective (algebraMap K (Rigidified.Baway (1 : K))) :=
    IsLocalization.injective _ (Submonoid.powers_le.2 (one_mem _))
  haveI : Nontrivial (Rigidified.Baway (1 : K)) := hS1.nontrivial
  have hpS : pIdeal p (Rigidified.Baway (1 : K)) = ⊥ := by
    refine Ideal.span_singleton_eq_bot.mpr ?_
    rw [← map_natCast (algebraMap K (Rigidified.Baway (1 : K))) p, CharP.cast_eq_zero, map_zero]
  haveI : Nontrivial (Rigidified.Baway (1 : K) ⧸ pIdeal p (Rigidified.Baway (1 : K))) :=
    Ideal.Quotient.nontrivial_iff.2 (by rw [hpS]; exact bot_ne_top)
  have hinj1 : Function.Injective (residueMap (p := p) (B := K) ψ') := by
    haveI : (pIdeal p (WittVector p k)).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (WittVector.irreducible p)
    letI : Field (WittVector p k ⧸ pIdeal p (WittVector p k)) := Ideal.Quotient.field _
    haveI : (pIdeal p K).IsMaximal := by rw [hpK]; exact Ideal.bot_isMaximal
    exact RingHom.injective _
  have hinj2 : Function.Injective (reduceMap (p := p) (Rigidified.awayHom (1 : K))) := by
    haveI : (pIdeal p K).IsMaximal := by rw [hpK]; exact Ideal.bot_isMaximal
    letI : Field (K ⧸ pIdeal p K) := Ideal.Quotient.field _
    exact RingHom.injective _
  have hbcinj : Function.Injective (Rigidified.bcPhi (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))) := by
    intro a b hab
    have hab' : MvFormalGroup.CartierModule.baseChange (Φ := (t'.Φbar ψ').F) (reduceMap (Rigidified.awayHom (1 : K)))
          (MvFormalGroup.CartierModule.baseChange (Φ := Φ.F) (residueMap ψ') a) =
        MvFormalGroup.CartierModule.baseChange (Φ := (t'.Φbar ψ').F) (reduceMap (Rigidified.awayHom (1 : K)))
          (MvFormalGroup.CartierModule.baseChange (Φ := Φ.F) (residueMap ψ') b) := hab
    exact MvFormalGroup.CartierModule.baseChangeEq_injective _ _ hinj1
      (MvFormalGroup.CartierModule.baseChangeEq_injective _ _ hinj2 hab')

  intro u u' huu
  dsimp only at huu
  have h0 : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).nMap ((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1) (Rigidified.bcPhi (Φ := Φ) ψ' (Rigidified.awayHom (1 : K)))
      (Rigidified.bcPhi_verschiebungInt (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))) (Rigidified.bcPhi_endAct_varpiEnd (Φ := Φ) ψ' (Rigidified.awayHom (1 : K)))
      (rΦ (u - u')) = 0 := by
    rw [map_sub, map_sub, sub_eq_zero]
    exact huu
  have h1 := (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).R1a_nsmul_eq_zero_of_nMap_eq_zero ((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1) (Rigidified.bcPhi (Φ := Φ) ψ' (Rigidified.awayHom (1 : K)))
      (Rigidified.bcPhi_verschiebungInt (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))) (Rigidified.bcPhi_endAct_varpiEnd (Φ := Φ) ψ' (Rigidified.awayHom (1 : K)))
      hbcinj _ h0
  have h2 : rΦ ((p : ℕ) • (u - u')) = 0 := by rw [map_nsmul, h1]
  have h3 : (p : ℕ) • (u - u') = 0 := hinjr (by rw [h2, map_zero])
  have h4 : u - u' = 0 := by
    funext i
    have hi : ((p : ℕ) : ℤ_[p]) * (u - u') i = 0 := by
      have := congrFun h3 i
      simpa [Pi.smul_apply, nsmul_eq_mul] using this
    exact (mul_eq_zero.mp hi).resolve_left (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  exact sub_eq_zero.mp h4

end S_CerednikDrinfeld_SpecialFormal_Rigidified_nMap_bcPhi_rPhi_injective_of_isAlgClosed
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_nMap_bcPhi_rPhi_injective_of_isAlgClosed (solution)
