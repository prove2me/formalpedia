-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.exists_submodule_forall_mem_iff_isEtaSection_of_isAdmissible_of_lieZero_le_ker_wittVector
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/c01a1551-9572-52b1-a205-ab5887291914

import Mathlib
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_lambda_injective_of_isHomogeneousVBasis_of_torsionFree
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isEtaSection_add_of_isAdmissible
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_forall_isEtaSection_zero_pow_smul_coe_of_isAdmissible
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_pow_smul_eq_coe_of_isEtaSection_zero_of_isAdmissible_of_lieZero_le_ker_wittVector
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

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_submodule_forall_mem_iff_isEtaSection_of_isAdmissible_of_lieZero_le_ker_wittVector
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt"

set_option autoImplicit false

p2m_open "CerednikDrinfeld P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_submodule_forall_mem_iff_isEtaSection_of_isAdmissible_of_lieZero_le_ker_wittVector.CerednikDrinfeld CerednikDrinfeld.SpecialFormal P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_submodule_forall_mem_iff_isEtaSection_of_isAdmissible_of_lieZero_le_ker_wittVector.CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega"

open scoped PadicInt Padic

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "Zp2 FormalODModule SpecialFormal.Rigidified GradedCartierModuleData SpecialFormal.Rigidified.exists_isEtaSection_add_of_isAdmissible SpecialFormal.Rigidified.exists_forall_isEtaSection_zero_pow_smul_coe_of_isAdmissible SpecialFormal.Rigidified.exists_pow_smul_eq_coe_of_isEtaSection_zero_of_isAdmissible_of_lieZero_le_ker_wittVector"
namespace GradedCartierModuleData
p2m_export "CerednikDrinfeld.GradedCartierModuleData" "lambda_injective_of_isHomogeneousVBasis_of_torsionFree IsHomogeneousVBasis varpi_varpi varpi module M verschiebung varpi_mem varpi_verschiebung varpi_frobenius NMod nMk nMk_surjective lambda lambda_nMk nVarpi nPiece nMap nMap_nMk IsCartierLMap IsCanonicalLMap phi phi_nMk mem_eta_iff etaPiece"
p2m_open "CerednikDrinfeld.GradedCartierModuleData CerednikDrinfeld"

variable {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] {j : Zp2 p →+* B}
variable (D : GradedCartierModuleData p B j)

private theorem _root_.CerednikDrinfeld.GradedCartierModuleData.QXA_nVarpi_nMk (m m' : D.M) : D.nVarpi (D.nMk (m, m')) = D.nMk (D.varpi m, D.varpi m') := rfl

p2m_export "CerednikDrinfeld.GradedCartierModuleData" "QXA_nVarpi_nMk"
theorem QXA_nVarpi_nVarpi (z : D.NMod) : D.nVarpi (D.nVarpi z) = (p : ℕ) • z := by
  obtain ⟨⟨m, m'⟩, rfl⟩ := D.nMk_surjective z
  rw [QXA_nVarpi_nMk, QXA_nVarpi_nMk, D.varpi_varpi, D.varpi_varpi, ← map_nsmul]
  rfl

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
theorem QXA_nVarpi_mem_etaPiece {L : D.M →+ D.NMod} (hL : D.IsCanonicalLMap L) {i : Fin 2}
    {z : D.NMod} (hz : z ∈ D.etaPiece L hL.isCartierLMap.map_verschiebung i) :
    D.nVarpi z ∈ D.etaPiece L hL.isCartierLMap.map_verschiebung (i + 1) := by
  refine AddSubgroup.mem_inf.2 ⟨?_, D.QXA_nVarpi_mem_nPiece (AddSubgroup.mem_inf.1 hz).2⟩
  rw [mem_eta_iff, D.QXA_phi_nVarpi hL, (D.mem_eta_iff _ _ _).1 (AddSubgroup.mem_inf.1 hz).1]

end CerednikDrinfeld.GradedCartierModuleData

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "Zp2 FormalODModule SpecialFormal.Rigidified GradedCartierModuleData SpecialFormal.Rigidified.exists_isEtaSection_add_of_isAdmissible SpecialFormal.Rigidified.exists_forall_isEtaSection_zero_pow_smul_coe_of_isAdmissible SpecialFormal.Rigidified.exists_pow_smul_eq_coe_of_isEtaSection_zero_of_isAdmissible_of_lieZero_le_ker_wittVector"
namespace SpecialFormal
p2m_export "CerednikDrinfeld.SpecialFormal" "pIdeal Rigidified Rigidified.exists_isEtaSection_add_of_isAdmissible Rigidified.jbar Rigidified.IsGradedPhiS Rigidified.isEtaSection_zero_iff Rigidified.isEtaSection_one_iff Rigidified.awayHom Rigidified.exists_forall_isEtaSection_zero_pow_smul_coe_of_isAdmissible Rigidified.exists_pow_smul_eq_coe_of_isEtaSection_zero_of_isAdmissible_of_lieZero_le_ker_wittVector"
namespace Rigidified
p2m_export "CerednikDrinfeld.SpecialFormal.Rigidified" "IsAdmissible map n exists_isEtaSection_add_of_isAdmissible jbar XS jS IsGradedS IsGradedSbar IsGradedPhiS LatticeRel IsEtaSection isEtaSection_zero_iff isEtaSection_one_iff awayHom exists_forall_isEtaSection_zero_pow_smul_coe_of_isAdmissible exists_pow_smul_eq_coe_of_isEtaSection_zero_of_isAdmissible_of_lieZero_le_ker_wittVector"
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

theorem QXA_LatticeRel_neg {p : ℕ} [Fact p.Prime] {S' : Type} [CommRing S'] {jS' : Zp2 p →+* S'}
    {E : GradedCartierModuleData p S' jS'} {n : ℕ} {r : (Fin 2 → ℤ_[p]) →+ E.NMod} {zbar : E.NMod}
    {v : Fin 2 → ℚ_[p]} (h : LatticeRel E n r zbar v) :
    LatticeRel E n r (-zbar) (-v) := by
  obtain ⟨m, k, w, hv, hr⟩ := h
  refine ⟨m, k, -w, ?_, ?_⟩
  · rw [smul_neg, hv]
    funext i
    simp only [Pi.neg_apply, PadicInt.coe_neg]
  · rw [map_neg, neg_nsmul, hr, neg_nsmul]

end CerednikDrinfeld.SpecialFormal.Rigidified

namespace ASUB_reduce

def toSubmodule {R V : Type} [Ring R] [AddCommGroup V] [Module R V] (A : AddSubgroup V)
    (h : ∀ (c : R) {v : V}, v ∈ A → c • v ∈ A) : Submodule R V where
  carrier := A
  add_mem' := A.add_mem
  zero_mem' := A.zero_mem
  smul_mem' := h

theorem mem_toSubmodule {R V : Type} [Ring R] [AddCommGroup V] [Module R V] (A : AddSubgroup V)
    (h : ∀ (c : R) {v : V}, v ∈ A → c • v ∈ A) (v : V) : v ∈ toSubmodule A h ↔ v ∈ A := Iff.rfl

theorem smul_mem_of_sandwich (p : ℕ) [Fact p.Prime] (A : AddSubgroup (Fin 2 → ℚ_[p])) (a B : ℕ)
    (hlow : ∀ w : Fin 2 → ℤ_[p], ((p : ℚ_[p]) ^ a • fun j => ((w j : ℤ_[p]) : ℚ_[p])) ∈ A)
    (hup : ∀ v ∈ A, ∃ w : Fin 2 → ℤ_[p], (p : ℚ_[p]) ^ B • v = fun j => ((w j : ℤ_[p]) : ℚ_[p]))
    (c : ℤ_[p]) {v : Fin 2 → ℚ_[p]} (hv : v ∈ A) : c • v ∈ A := by
  obtain ⟨w, hw⟩ := hup v hv
  obtain ⟨c', hc'⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec (a + B) c)
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero

  have key : c • v = (PadicInt.appr c (a + B) : ℕ) • v +
      (p : ℚ_[p]) ^ a • fun j => (((c' * w j : ℤ_[p]) : ℚ_[p])) := by
    have hcv : c • v = ((PadicInt.appr c (a + B) : ℕ) : ℤ_[p]) • v + (c' * (p : ℤ_[p]) ^ (a + B)) • v := by
      rw [← add_smul, hc', add_sub_cancel]
    rw [hcv, Nat.cast_smul_eq_nsmul]
    congr 1
    funext j
    have hwj := congr_fun hw j
    simp only [Pi.smul_apply, smul_eq_mul] at hwj ⊢
    rw [Algebra.smul_def]
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_pow, map_natCast, PadicInt.coe_mul]
    rw [← hwj]
    have : (algebraMap ℤ_[p] ℚ_[p]) c' = (c' : ℚ_[p]) := rfl
    rw [this]
    ring
  rw [key]
  exact A.add_mem (A.nsmul_mem hv _) (hlow _)

end ASUB_reduce

open ASUB_reduce _root_.CerednikDrinfeld.GradedCartierModuleData _root_.P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_submodule_forall_mem_iff_isEtaSection_of_isAdmissible_of_lieZero_le_ker_wittVector.CerednikDrinfeld.GradedCartierModuleData in
theorem solution
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
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
    {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : WittVector p k →+* B)
    (hB : IsNilpotent (p : B))
    (t : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ) :
    ∃ (N₀ N₁ : PrimeSpectrum B → Submodule ℤ_[p] (Fin 2 → ℚ_[p])),
      (∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]), v ∈ N₀ x ↔
          ∃ (f : B) (_ : f ∉ x.asIdeal) (hc : t.IsGradedS ι ψ (Rigidified.awayHom f))
            (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f)) (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
            (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L),
            ∃ z, t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL 0 z v) ∧
      (∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]), v ∈ N₁ x ↔
          ∃ (f : B) (_ : f ∉ x.asIdeal) (hc : t.IsGradedS ι ψ (Rigidified.awayHom f))
            (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f)) (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
            (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L),
            ∃ z, t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL 1 z v) := by

  obtain ⟨P, hP⟩ : ∃ P : PrimeSpectrum B → Fin 2 → (Fin 2 → ℚ_[p]) → Prop,
      ∀ (x : PrimeSpectrum B) (i : Fin 2) (v : Fin 2 → ℚ_[p]), P x i v ↔
          ∃ (f : B) (_ : f ∉ x.asIdeal) (hc : t.IsGradedS ι ψ (Rigidified.awayHom f))
            (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f)) (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
            (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L),
            ∃ z, t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL i z v := ⟨_, fun _ _ _ => Iff.rfl⟩
  have hPLUS := CerednikDrinfeld.SpecialFormal.Rigidified.exists_isEtaSection_add_of_isAdmissible p ι Φ hΦ hΦ4 hcΦ rΦ hLΦ hrΦ ψ hB t ht
  have hLOW := CerednikDrinfeld.SpecialFormal.Rigidified.exists_forall_isEtaSection_zero_pow_smul_coe_of_isAdmissible p ι Φ hΦ hΦ4 hcΦ rΦ hLΦ hrΦ ψ hB t ht
  have hUP := CerednikDrinfeld.SpecialFormal.Rigidified.exists_pow_smul_eq_coe_of_isEtaSection_zero_of_isAdmissible_of_lieZero_le_ker_wittVector p k ι Φ hΦ hΦ4 h0Φ hcΦ rΦ hLΦ hrΦ ψ hB t ht

  have h01 : ∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]), P x 0 v → P x 1 v := by
    intro x v hv
    obtain ⟨f, hf, hc, hcb, hcΦf, L, hL, z, hz⟩ := (hP x 0 v).1 hv
    rw [Rigidified.isEtaSection_zero_iff] at hz
    refine (hP x 1 v).2 ⟨f, hf, hc, hcb, hcΦf, L, hL, ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).nVarpi z, ?_⟩
    rw [Rigidified.isEtaSection_one_iff]
    refine ⟨by simpa using QXA_nVarpi_mem_etaPiece _ hL hz.1, ?_⟩
    rw [QXA_nVarpi_nVarpi, map_nsmul]
    exact Rigidified.QXA_LatticeRel_smul hz.2
  have h10 : ∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]), P x 1 v → P x 0 ((p : ℚ_[p]) • v) := by
    intro x v hv
    obtain ⟨f, hf, hc, hcb, hcΦf, L, hL, z, hz⟩ := (hP x 1 v).1 hv
    rw [Rigidified.isEtaSection_one_iff] at hz
    refine (hP x 0 _).2 ⟨f, hf, hc, hcb, hcΦf, L, hL, ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).nVarpi z, ?_⟩
    rw [Rigidified.isEtaSection_zero_iff]
    exact ⟨by simpa using QXA_nVarpi_mem_etaPiece _ hL hz.1, hz.2⟩

  have hneg : ∀ (x : PrimeSpectrum B) (i : Fin 2) (v : Fin 2 → ℚ_[p]), P x i v → P x i (-v) := by
    intro x i v hv
    obtain ⟨f, hf, hc, hcb, hcΦf, L, hL, z, hz⟩ := (hP x i v).1 hv
    refine (hP x i _).2 ⟨f, hf, hc, hcb, hcΦf, L, hL, -z, ?_⟩
    refine ⟨neg_mem hz.1, ?_⟩
    rw [map_neg, map_neg, smul_neg]
    exact Rigidified.QXA_LatticeRel_neg hz.2

  have hzero : ∀ (x : PrimeSpectrum B) (i : Fin 2), P x i 0 := by
    intro x i
    obtain ⟨a, ha⟩ := hLOW x
    have e0 : ((p : ℚ_[p]) ^ a • fun j => (((0 : Fin 2 → ℤ_[p]) j : ℤ_[p]) : ℚ_[p])) = 0 := by
      funext j
      simp only [Pi.smul_apply, Pi.zero_apply, PadicInt.coe_zero, smul_zero]
    have h0 : P x 0 0 := e0 ▸ (hP x 0 _).2 (ha 0)
    fin_cases i
    · exact h0
    · exact h01 x 0 h0

  let A : PrimeSpectrum B → Fin 2 → AddSubgroup (Fin 2 → ℚ_[p]) := fun x i =>
    { carrier := {v | P x i v}
      zero_mem' := hzero x i
      add_mem' := fun {v v'} hv hv' => (hP x i _).2 (hPLUS x i v v' ((hP x i v).1 hv) ((hP x i v').1 hv'))
      neg_mem' := fun {v} hv => hneg x i v hv }
  have hA : ∀ x i v, v ∈ A x i ↔ P x i v := fun _ _ _ => Iff.rfl

  have hsmul : ∀ (x : PrimeSpectrum B) (i : Fin 2) (c : ℤ_[p]) {v : Fin 2 → ℚ_[p]},
      v ∈ A x i → c • v ∈ A x i := by
    intro x i
    obtain ⟨a, ha⟩ := hLOW x
    obtain ⟨b, hb⟩ := hUP x
    refine smul_mem_of_sandwich p (A x i) a (b + 1) (fun w => ?_) (fun v hv => ?_)
    · refine (hA x i _).2 ?_
      have hw0 : P x 0 ((p : ℚ_[p]) ^ a • fun j => ((w j : ℤ_[p]) : ℚ_[p])) := (hP x 0 _).2 (ha w)
      fin_cases i
      · exact hw0
      · exact h01 x _ hw0
    · have hv' := (hA x i v).1 hv
      fin_cases i
      · obtain ⟨w, hw⟩ := hb v ((hP x 0 v).1 hv')
        refine ⟨fun j => (p : ℤ_[p]) * w j, ?_⟩
        rw [pow_succ, mul_comm, ← smul_smul, hw]
        funext j
        simp only [Pi.smul_apply, smul_eq_mul, PadicInt.coe_mul, PadicInt.coe_natCast]
      · obtain ⟨w, hw⟩ := hb _ ((hP x 0 _).1 (h10 x v hv'))
        exact ⟨w, by rw [pow_succ, ← smul_smul, hw]⟩
  refine ⟨fun x => toSubmodule (A x 0) (hsmul x 0), fun x => toSubmodule (A x 1) (hsmul x 1),
    fun x v => ?_, fun x v => ?_⟩
  · rw [mem_toSubmodule, hA]; exact hP x 0 v
  · rw [mem_toSubmodule, hA]; exact hP x 1 v

end S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_submodule_forall_mem_iff_isEtaSection_of_isAdmissible_of_lieZero_le_ker_wittVector
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_submodule_forall_mem_iff_isEtaSection_of_isAdmissible_of_lieZero_le_ker_wittVector (solution)
