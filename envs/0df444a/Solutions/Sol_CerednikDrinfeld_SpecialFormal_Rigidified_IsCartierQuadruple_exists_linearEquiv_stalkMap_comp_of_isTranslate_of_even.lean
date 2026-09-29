-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.exists_linearEquiv_stalkMap_comp_of_isTranslate_of_even
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/ebad4488-0faf-52d0-9f15-e23dbb57bdd0

import Mathlib
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_nsmul_nMap_rigidNum_translate_eq_nsmul_rigidNum_mulVec
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_nsmul_iterate_nMap_verschiebung_eq_nsmul_iterate_nVarpi_of_mem_eta
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_nsmul_nMap_mem_eta_of_mem_eta_of_cast_eq_zero
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isCanonicalLMap_toGradedCartierModuleData
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isHomogeneousVBasis_of_isHomogeneousVBasis_toGradedCartierModuleData
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isBaseChangeAlong_toGradedCartierModuleData_baseChange
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isCompl_gradedPiece_zero_one_of_isNilpotent
import Theorems.Thm_WittVector_ringHom_map_frobenius_of_finite
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
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_exists_linearEquiv_stalkMap_comp_of_isTranslate_of_even
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt"

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic Matrix

namespace B28SM

variable {p : ℕ} [Fact p.Prime]

theorem frobenius_frobenius_zp2 (x : Zp2 p) :
    WittVector.frobenius (WittVector.frobenius x) = x := by
  ext n
  simp only [WittVector.coeff_frobenius_charP]
  letI : Fintype (GaloisField p 2) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField p 2) = p ^ 2 := by
    rw [Fintype.card_eq_nat_card, GaloisField.card p 2 two_ne_zero]
  rw [← pow_mul, ← pow_two, ← hcard]; exact FiniteField.pow_card _

theorem frobenius_pow_two_mul_zp2 (j : ℕ) (x : Zp2 p) :
    ((WittVector.frobenius : Zp2 p →+* Zp2 p) ^ (2 * j)) x = x := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Nat.mul_succ, pow_add, RingHom.mul_def, RingHom.comp_apply, pow_two, RingHom.mul_def, RingHom.comp_apply,
      frobenius_frobenius_zp2, ih]

theorem frobenius_pow_comp_eq (k : Type) [Field k] [CharP k p] [PerfectRing k p]
    (ι : Zp2 p →+* WittVector p k) (n : ℕ) (x : Zp2 p) :
    ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ n) (ι x) =
      ι (((WittVector.frobenius : Zp2 p →+* Zp2 p) ^ n) x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', RingHom.mul_def, RingHom.comp_apply, ih, pow_succ', RingHom.mul_def, RingHom.comp_apply,
      WittVector.ringHom_map_frobenius_of_finite]

theorem structureMap_comp_frobenius_pow_two_mul (k : Type) [Field k] [CharP k p] [PerfectRing k p]
    (ι : Zp2 p →+* WittVector p k) {B : Type} [CommRing B] (ψ : WittVector p k →+* B) (j : ℕ) :
    structureMap ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j))) = structureMap ι ψ := by
  refine RingHom.ext fun x => ?_
  show ψ (((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j)) (ι x)) = ψ (ι x)
  rw [frobenius_pow_comp_eq, frobenius_pow_two_mul_zp2]

end B28SM

namespace B28LE

open CerednikDrinfeld.FormalODModule MvFormalGroup MvFormalGroup.CartierModule

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O]

section
variable (ι : Zp2 p →+* O) {Φ : FormalODModule p (O ⧸ pIdeal p O)}
  (hcΦ : IsCompl (Φ.gradedPiece (Rigidified.jbar ι) 0) (Φ.gradedPiece (Rigidified.jbar ι) 1))
  (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
  {B : Type} [CommRing B] (ψ : O →+* B) (t : Rigidified p Φ B)
  (hOD : IsODHom (t.Φbar ψ) t.Xbar t.ρ) {S : Type} [CommRing S] (g : B →+* S)

def PresJ (jB : Zp2 p →+* B) (i : Fin 2) (v : Fin 2 → ℚ_[p]) : Prop :=
  ∃ (hc : IsCompl ((t.XS g).gradedPiece (g.comp jB) 0) ((t.XS g).gradedPiece (g.comp jB) 1))
    (hcb : IsCompl ((t.XbarS g).gradedPiece ((reduceMap g).comp ((Ideal.Quotient.mk (pIdeal p B)).comp jB)) 0)
      ((t.XbarS g).gradedPiece ((reduceMap g).comp ((Ideal.Quotient.mk (pIdeal p B)).comp jB)) 1))
    (hcΦg : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ g)
    (L : ((t.XS g).toGradedCartierModuleData (g.comp jB) hc).M →+
      ((t.XS g).toGradedCartierModuleData (g.comp jB) hc).NMod)
    (hL : ((t.XS g).toGradedCartierModuleData (g.comp jB) hc).IsCanonicalLMap L),
    ∃ z : ((t.XS g).toGradedCartierModuleData (g.comp jB) hc).NMod,
      z ∈ ((t.XS g).toGradedCartierModuleData (g.comp jB) hc).etaPiece L hL.isCartierLMap.map_verschiebung i ∧
      Rigidified.LatticeRel ((t.XbarS g).toGradedCartierModuleData
          ((reduceMap g).comp ((Ideal.Quotient.mk (pIdeal p B)).comp jB)) hcb) t.n
        ((((Rigidified.PhibarS (Φ := Φ) ψ g).toGradedCartierModuleData (Rigidified.jPhiS ι ψ g) hcΦg).nMap
            ((t.XbarS g).toGradedCartierModuleData ((reduceMap g).comp ((Ideal.Quotient.mk (pIdeal p B)).comp jB)) hcb)
            (Rigidified.rhoC ψ t hOD.1 g) (Rigidified.rhoC_verschiebungInt ψ t hOD.1 g)
            (Rigidified.rhoC_endAct_varpiEnd ψ t hOD g)).comp
          (((Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).nMap
              ((Rigidified.PhibarS (Φ := Φ) ψ g).toGradedCartierModuleData (Rigidified.jPhiS ι ψ g) hcΦg)
              (Rigidified.bcPhi (Φ := Φ) ψ g) (Rigidified.bcPhi_verschiebungInt (Φ := Φ) ψ g)
              (Rigidified.bcPhi_endAct_varpiEnd (Φ := Φ) ψ g)).comp rΦ))
        (((t.XS g).toGradedCartierModuleData (g.comp jB) hc).nMap
          ((t.XbarS g).toGradedCartierModuleData ((reduceMap g).comp ((Ideal.Quotient.mk (pIdeal p B)).comp jB)) hcb)
          (t.redC g) (t.redC_verschiebungInt g) (t.redC_endAct_varpiEnd g)
          (((((t.XS g).toGradedCartierModuleData (g.comp jB) hc).nVarpi :
              ((t.XS g).toGradedCartierModuleData (g.comp jB) hc).NMod →ₗ[WittVector p S]
                ((t.XS g).toGradedCartierModuleData (g.comp jB) hc).NMod) ^ (i : ℕ)) z))
        ((p : ℚ_[p]) ^ (i : ℕ) • v)

theorem exists_isEtaSection_iff_presJ (jB : Zp2 p →+* B) (hjB : structureMap ι ψ = jB)
    (i : Fin 2) (v : Fin 2 → ℚ_[p]) :
    (∃ (hc : t.IsGradedS ι ψ g) (hcb : t.IsGradedSbar ι ψ g) (hcΦg : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ g)
        (L : _) (hL : ((t.XS g).toGradedCartierModuleData _ hc).IsCanonicalLMap L),
        ∃ z, t.IsEtaSection ι hcΦ rΦ ψ hOD g hc hcb hcΦg L hL i z v) ↔
      PresJ ι hcΦ rΦ ψ t hOD g jB i v := by
  subst hjB
  exact Iff.rfl

end

end B28LE

namespace LE6

open CerednikDrinfeld.GradedCartierModuleData

section NMod

variable {p : ℕ} [hp : Fact p.Prime] {B : Type} [CommRing B] {j : Zp2 p →+* B}
variable (D : GradedCartierModuleData p B j)

noncomputable def nu : D.NMod →+ D.NMod :=
  D.nMap D D.verschiebung (fun _ => rfl) (fun x => (D.varpi_verschiebung x).symm)

theorem nu_nMk (m m' : D.M) : nu D (D.nMk (m, m')) = D.nMk (D.verschiebung m, D.verschiebung m') := rfl

theorem nu_iterate_nMk (n : ℕ) (m m' : D.M) :
    (⇑(nu D))^[n] (D.nMk (m, m')) = D.nMk ((⇑D.verschiebung)^[n] m, (⇑D.verschiebung)^[n] m') := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, nu_nMk, Function.iterate_succ_apply', Function.iterate_succ_apply']

noncomputable def nuF (hVF : ∀ x : D.M, D.verschiebung (D.frobenius x) = (p : ℕ) • x) : D.NMod →+ D.NMod :=
  D.nMap D D.frobenius (fun x => by rw [D.frobenius_verschiebung, hVF]) (fun x => (D.varpi_frobenius x).symm)

theorem nuF_nu (hVF : ∀ x : D.M, D.verschiebung (D.frobenius x) = (p : ℕ) • x) (y : D.NMod) :
    nuF D hVF (nu D y) = (p : ℕ) • y := by
  obtain ⟨⟨m, m'⟩, rfl⟩ := D.nMk_surjective y
  rw [nu_nMk, nuF, nMap_nMk, D.frobenius_verschiebung, D.frobenius_verschiebung, ← map_nsmul]
  rfl

theorem nVarpi_nMk (m m' : D.M) : D.nVarpi (D.nMk (m, m')) = D.nMk (D.varpi m, D.varpi m') := rfl

theorem nVarpi_nVarpi (z : D.NMod) : D.nVarpi (D.nVarpi z) = (p : ℕ) • z := by
  obtain ⟨⟨m, m'⟩, rfl⟩ := D.nMk_surjective z
  rw [nVarpi_nMk, nVarpi_nMk, D.varpi_varpi, D.varpi_varpi, ← map_nsmul]
  rfl

theorem nu_nVarpi (z : D.NMod) : nu D (D.nVarpi z) = D.nVarpi (nu D z) := by
  obtain ⟨⟨m, m'⟩, rfl⟩ := D.nMk_surjective z
  rw [nVarpi_nMk, nu_nMk, nu_nMk, nVarpi_nMk, D.varpi_verschiebung, D.varpi_verschiebung]

theorem commute_nu_nVarpi : Function.Commute (nu D) D.nVarpi := fun z => nu_nVarpi D z

theorem nMap_nVarpi {B' : Type} [CommRing B'] {j' : Zp2 p →+* B'} (D' : GradedCartierModuleData p B' j')
    (f : D.M →+ D'.M) (hV : ∀ x, f (D.verschiebung x) = D'.verschiebung (f x))
    (hPi : ∀ x, f (D.varpi x) = D'.varpi (f x)) (z : D.NMod) :
    D.nMap D' f hV hPi (D.nVarpi z) = D'.nVarpi (D.nMap D' f hV hPi z) := by
  obtain ⟨⟨m, m'⟩, rfl⟩ := D.nMk_surjective z
  rw [nVarpi_nMk, nMap_nMk, nMap_nMk, nVarpi_nMk, hPi, hPi]

theorem nMap_nVarpi_pow {B' : Type} [CommRing B'] {j' : Zp2 p →+* B'} (D' : GradedCartierModuleData p B' j')
    (f : D.M →+ D'.M) (hV : ∀ x, f (D.verschiebung x) = D'.verschiebung (f x))
    (hPi : ∀ x, f (D.varpi x) = D'.varpi (f x)) (n : ℕ) (z : D.NMod) :
    D.nMap D' f hV hPi ((D.nVarpi ^ n) z) = (⇑D'.nVarpi)^[n] (D.nMap D' f hV hPi z) := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, ih, nMap_nVarpi, Function.iterate_succ_apply]

omit hp in
theorem iterate_map_nsmul {M : Type} [AddCommMonoid M] {F : Type} [FunLike F M M] [AddMonoidHomClass F M M]
    (f : F) (n k : ℕ) (x : M) : (⇑f)^[n] (k • x) = k • (⇑f)^[n] x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, map_nsmul, ih]

theorem nVarpi_iterate_two_mul (n : ℕ) (z : D.NMod) : (⇑D.nVarpi)^[2 * n] z = p ^ n • z := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 + 2 * n by ring, Function.iterate_add_apply, ih,
      show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_add_apply, Function.iterate_one,
      map_nsmul, map_nsmul, nVarpi_nVarpi, smul_smul, ← pow_succ]

theorem nuF_iterate_nu_iterate (hVF : ∀ x : D.M, D.verschiebung (D.frobenius x) = (p : ℕ) • x) (n : ℕ)
    (y : D.NMod) : (⇑(nuF D hVF))^[n] ((⇑(nu D))^[n] y) = p ^ n • y := by
  induction n generalizing y with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply', nuF_nu, iterate_map_nsmul, ih, smul_smul,
      ← pow_succ']

theorem key (hVF : ∀ x : D.M, D.verschiebung (D.frobenius x) = (p : ℕ) • x)
    (L : D.M →+ D.NMod) (hL : D.IsCartierLMap L) (y : D.NMod)
    (hy : (p : ℕ) • y ∈ D.eta L hL.map_verschiebung) (j i : ℕ) :
    p ^ 2 • (⇑(nu D))^[2 * j] ((⇑D.nVarpi)^[i] y) = p ^ (2 + j) • (⇑D.nVarpi)^[i] y := by
  have h := CerednikDrinfeld.GradedCartierModuleData.nsmul_iterate_nMap_verschiebung_eq_nsmul_iterate_nVarpi_of_mem_eta
    p D hVF L hL (nu D) (fun x y => rfl) (2 * j) ((p : ℕ) • y) hy
  rw [iterate_map_nsmul, iterate_map_nsmul, nVarpi_iterate_two_mul, smul_smul, smul_smul, smul_smul,
    ← pow_two] at h

  rw [(commute_nu_nVarpi D).iterate_iterate (2 * j) i y,
    ← iterate_map_nsmul D.nVarpi i (p ^ 2) ((⇑(nu D))^[2 * j] y), h, iterate_map_nsmul, ← pow_add]

end NMod

section Vectors

variable {p : ℕ} [hp : Fact p.Prime]

theorem exists_pow_mul_norm_le_one (x : ℚ_[p]) : ∃ N : ℕ, ‖(p : ℚ_[p]) ^ N * x‖ ≤ 1 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt ‖x‖ hp1
  refine ⟨N, ?_⟩
  rw [norm_mul, norm_pow, Padic.norm_p, inv_pow, inv_mul_le_iff₀ (by positivity), mul_one]
  exact hN.le

theorem norm_pow_p_mul_le_one {x : ℚ_[p]} (hx : ‖x‖ ≤ 1) (N : ℕ) : ‖(p : ℚ_[p]) ^ N * x‖ ≤ 1 := by
  rw [norm_mul, norm_pow, Padic.norm_p]
  have h1 : ((p : ℝ)⁻¹) ^ N ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (by exact_mod_cast hp.out.one_lt.le))
  calc ((p : ℝ)⁻¹) ^ N * ‖x‖ ≤ 1 * 1 := mul_le_mul h1 hx (norm_nonneg _) zero_le_one
    _ = 1 := one_mul _

theorem exists_pow_smul_eq_coe (v : Fin 2 → ℚ_[p]) :
    ∃ (N : ℕ) (w : Fin 2 → ℤ_[p]), (p : ℚ_[p]) ^ N • v = fun i => ((w i : ℤ_[p]) : ℚ_[p]) := by
  obtain ⟨N0, h0⟩ := exists_pow_mul_norm_le_one (v 0)
  obtain ⟨N1, h1⟩ := exists_pow_mul_norm_le_one (v 1)
  have h0' : ‖(p : ℚ_[p]) ^ (N0 + N1) * v 0‖ ≤ 1 := by
    rw [add_comm, pow_add, mul_assoc]; exact norm_pow_p_mul_le_one h0 N1
  have h1' : ‖(p : ℚ_[p]) ^ (N0 + N1) * v 1‖ ≤ 1 := by
    rw [pow_add, mul_assoc]; exact norm_pow_p_mul_le_one h1 N0
  refine ⟨N0 + N1, fun i => if h : i = 0 then ⟨_, h0'⟩ else ⟨_, h1'⟩, ?_⟩
  funext i
  fin_cases i
  · rfl
  · rfl

theorem coe_injective_vec {w w' : Fin 2 → ℤ_[p]}
    (h : (fun i => ((w i : ℤ_[p]) : ℚ_[p])) = fun i => ((w' i : ℤ_[p]) : ℚ_[p])) : w = w' :=
  funext fun i => Subtype.ext (congrFun h i)

theorem coe_nsmul_vec (k : ℕ) (w : Fin 2 → ℤ_[p]) :
    (fun i => (((k • w) i : ℤ_[p]) : ℚ_[p])) = (k : ℚ_[p]) • fun i => ((w i : ℤ_[p]) : ℚ_[p]) := by
  funext i
  simp [nsmul_eq_mul, Pi.smul_apply]

theorem coe_mulVec (A : Matrix (Fin 2) (Fin 2) ℤ_[p]) (w : Fin 2 → ℤ_[p]) :
    (fun i => (((A *ᵥ w) i : ℤ_[p]) : ℚ_[p])) = (A.map ((↑) : ℤ_[p] → ℚ_[p])) *ᵥ fun i => ((w i : ℤ_[p]) : ℚ_[p]) := by
  funext i
  exact RingHom.map_mulVec PadicInt.Coe.ringHom A w i

omit hp in

theorem mem_latticeMap_iff_inv_mulVec_mem {R K : Type} [CommRing R] [Field K] [Algebra R K]
    (h : Matrix.GeneralLinearGroup (Fin 2) K) (N : Submodule R (Fin 2 → K)) (v : Fin 2 → K) :
    v ∈ latticeMap h N ↔ ((h⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v ∈ N := by
  rw [mem_latticeMap]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rwa [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  · intro hv
    exact ⟨_, hv, by rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]⟩

omit hp in
theorem scalarGL_inv {K : Type} [Field K] (c : Kˣ) :
    (scalarGL c : Matrix.GeneralLinearGroup (Fin 2) K)⁻¹ = scalarGL c⁻¹ :=
  Units.ext rfl

omit hp in

theorem inv_scalarGL_mul_inv_mulVec {K : Type} [Field K] (c : Kˣ) (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (v : Fin 2 → K) :
    (((scalarGL c * g⁻¹)⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v =
      ((c⁻¹ : Kˣ) : K) • ((g : Matrix (Fin 2) (Fin 2) K) *ᵥ v) := by
  rw [mul_inv_rev, inv_inv, scalarGL_inv, Units.val_mul, ← Matrix.mulVec_mulVec, scalarGL_mulVec,
    Matrix.mulVec_smul]

end Vectors

section WittFacts

variable {p : ℕ} [hp : Fact p.Prime]

theorem wittVector_verschiebung_one_eq_natCast {B : Type} [CommRing B] (hp0 : (p : B) = 0) :
    (WittVector.verschiebung (1 : WittVector p B)) = (p : WittVector p B) := by
  rcases subsingleton_or_nontrivial B with hB | hB
  · ext n; exact Subsingleton.elim _ _
  · haveI : CharP B p := (CharP.charP_iff_prime_eq_zero hp.out).mpr hp0
    ext n
    rw [WittVector.coeff_p]
    cases n with
    | zero => rw [WittVector.verschiebung_coeff_zero, if_neg (Nat.zero_ne_one)]
    | succ n =>
      rw [WittVector.verschiebung_coeff_succ]
      cases n with
      | zero => rw [if_pos rfl, WittVector.one_coeff_zero]
      | succ n => rw [if_neg (by omega), WittVector.one_coeff_eq_of_pos]; exact Nat.succ_pos _

theorem verschiebung_frobenius_eq_nsmul {B : Type} [CommRing B] {j : Zp2 p →+* B}
    (D : GradedCartierModuleData p B j) (hp0 : (p : B) = 0) (x : D.M) :
    D.verschiebung (D.frobenius x) = (p : ℕ) • x := by
  rw [D.verschiebung_frobenius, wittVector_verschiebung_one_eq_natCast hp0, Nat.cast_smul_eq_nsmul]

omit hp in
theorem isHausdorff_of_isNilpotent {S : Type} [CommRing S] (hS : IsNilpotent ((p : ℕ) : S)) :
    IsHausdorff (Ideal.span {((p : ℕ) : S)}) S := by
  obtain ⟨N, hN⟩ := hS
  refine ⟨fun x hx => ?_⟩
  have := hx N
  rwa [Ideal.span_singleton_pow, hN, Ideal.span_singleton_eq_bot.mpr rfl, Submodule.bot_smul, SModEq.bot] at this

end WittFacts

section LBar

open MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld.SpecialFormal.Rigidified

variable {p : ℕ} [hp : Fact p.Prime]

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

theorem exists_isCanonicalLMap_bar {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    {Φ : FormalODModule p (O ⧸ pIdeal p O)} {B : Type} [CommRing B] (ψ : O →+* B) (t : Rigidified p Φ B)
    {S : Type} [CommRing S] [Algebra ℤ_[p] S] (g : B →+* S)
    (hc : t.IsGradedS ι ψ g) (hcb : t.IsGradedSbar ι ψ g)
    (L : _) (hL : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).IsCanonicalLMap L) :
    ∃ Lb : ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).M →+
        ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).NMod,
      ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).IsCanonicalLMap Lb := by
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
  have hbca : IsBaseChangeAlong' (Ideal.Quotient.mk (pIdeal p S))
      ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc)
      ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb)
      (CartierModule.baseChangeEq (Ideal.Quotient.mk (pIdeal p S)) hF) :=
    isBaseChangeAlong'_of_eq _ _ _ _ hγ hc _ hXm _ hjb hcb hF
  have hγb : (t.XbarS g).IsHomogeneousVBasis (Rigidified.jSbar ι ψ g)
      (fun i => CartierModule.baseChangeEq (Ideal.Quotient.mk (pIdeal p S)) hF (fl (γl i))) := by
    refine ⟨fun i => ?_, isUnit_det_tangent_baseChangeEq _ hF _ hγ.2⟩
    exact (FormalODModule.mem_toGradedCartierModuleData_piece_iff _ _ hcb i _).mp
      (hbca.2.2.2.2.1 i _ ((FormalODModule.mem_toGradedCartierModuleData_piece_iff _ _ hc i _).mpr (hγ.1 i)))
  exact CerednikDrinfeld.FormalODModule.exists_isCanonicalLMap_toGradedCartierModuleData p
    (Rigidified.jSbar ι ψ g) (isHausdorff_of_isNilpotent hp0) _ _ hγb hcb

end LBar

section Core

variable {p : ℕ} [hp : Fact p.Prime]

theorem core {S : Type} [CommRing S] {jE : Zp2 p →+* S} (E : GradedCartierModuleData p S jE)
    (hVF : ∀ x : E.M, E.verschiebung (E.frobenius x) = (p : ℕ) • x)
    (Lb : E.M →+ E.NMod) (hLb : E.IsCartierLMap Lb)
    (y : E.NMod) (hy : (p : ℕ) • y ∈ E.eta Lb hLb.map_verschiebung) (i : ℕ)
    (r r' : (Fin 2 → ℤ_[p]) →+ E.NMod) (A : Matrix (Fin 2) (Fin 2) ℤ_[p])
    (j a b d n n' : ℕ) (habd : b + n + d = a + n' + j)
    (hG4 : ∀ w, p ^ a • (⇑(nu E))^[2 * j] (r' w) = p ^ b • r (A *ᵥ w))
    (V U : Fin 2 → ℚ_[p]) (hAVU : (A.map ((↑) : ℤ_[p] → ℚ_[p])) *ᵥ V = (p : ℚ_[p]) ^ d • U) :
    Rigidified.LatticeRel E n' r' ((⇑E.nVarpi)^[i] y) V ↔ Rigidified.LatticeRel E n r ((⇑E.nVarpi)^[i] y) U := by
  have hkey := key E hVF Lb hLb y hy j i
  constructor
  · rintro ⟨m0, k0, w, hw, hr⟩
    refine ⟨m0 + d, 2 + k0 + b, A *ᵥ w, ?_, ?_⟩
    · rw [coe_mulVec, ← hw, Matrix.mulVec_smul, hAVU, smul_smul, ← pow_add, add_comm]
    · calc p ^ (2 + k0 + b) • r (A *ᵥ w)
            = p ^ (2 + k0) • (p ^ b • r (A *ᵥ w)) := by rw [smul_smul, ← pow_add]
        _ = p ^ (2 + k0) • (p ^ a • (⇑(nu E))^[2 * j] (r' w)) := by rw [hG4]
        _ = p ^ (2 + a) • (⇑(nu E))^[2 * j] (p ^ k0 • r' w) := by
              rw [iterate_map_nsmul, smul_smul, smul_smul, show p ^ (2 + k0) * p ^ a = p ^ (2 + a) * p ^ k0 by ring]
        _ = p ^ (2 + a) • (⇑(nu E))^[2 * j] (p ^ (k0 + n' + m0) • (⇑E.nVarpi)^[i] y) := by rw [hr]
        _ = p ^ (a + k0 + n' + m0) • (p ^ 2 • (⇑(nu E))^[2 * j] ((⇑E.nVarpi)^[i] y)) := by
              rw [iterate_map_nsmul, smul_smul, smul_smul,
                show p ^ (2 + a) * p ^ (k0 + n' + m0) = p ^ (a + k0 + n' + m0) * p ^ 2 by ring]
        _ = p ^ (a + k0 + n' + m0) • (p ^ (2 + j) • (⇑E.nVarpi)^[i] y) := by rw [hkey]
        _ = p ^ (2 + k0 + b + n + (m0 + d)) • (⇑E.nVarpi)^[i] y := by
              rw [smul_smul, ← pow_add, show a + k0 + n' + m0 + (2 + j) = 2 + k0 + b + n + (m0 + d) by omega]
  · rintro ⟨m1, k1, w1, hw1, hr1⟩
    obtain ⟨N0, w0, hw0⟩ := exists_pow_smul_eq_coe V
    have hAw : A *ᵥ (p ^ m1 • w0) = p ^ (N0 + d) • w1 := by
      apply coe_injective_vec
      rw [coe_mulVec, coe_nsmul_vec, coe_nsmul_vec, ← hw0, ← hw1, Matrix.mulVec_smul, Matrix.mulVec_smul, hAVU,
        smul_smul, smul_smul, smul_smul, Nat.cast_pow, Nat.cast_pow, ← pow_add, ← pow_add, ← pow_add,
        show m1 + N0 + d = N0 + d + m1 by omega]
    have hG4w := hG4 (p ^ m1 • w0)
    rw [hAw, map_nsmul r (p ^ (N0 + d)) w1, smul_smul, ← pow_add] at hG4w

    refine ⟨m1 + N0, 2 * j + (2 + j + k1 + a), p ^ m1 • w0, ?_, ?_⟩
    · rw [coe_nsmul_vec, ← hw0, smul_smul, Nat.cast_pow, ← pow_add]
    · have step : (⇑(nu E))^[2 * j] (p ^ (2 + j + k1 + a) • r' (p ^ m1 • w0)) =
          (⇑(nu E))^[2 * j] (p ^ (b + N0 + d + k1 + n + m1 + 2) • (⇑E.nVarpi)^[i] y) := by
        calc (⇑(nu E))^[2 * j] (p ^ (2 + j + k1 + a) • r' (p ^ m1 • w0))
              = p ^ (2 + j + k1) • (p ^ a • (⇑(nu E))^[2 * j] (r' (p ^ m1 • w0))) := by
                  rw [iterate_map_nsmul, smul_smul, ← pow_add]
          _ = p ^ (2 + j + k1) • (p ^ (b + (N0 + d)) • r w1) := by rw [hG4w]
          _ = p ^ (2 + j + b + N0 + d) • (p ^ k1 • r w1) := by
                  rw [smul_smul, smul_smul, show p ^ (2 + j + k1) * p ^ (b + (N0 + d)) = p ^ (2 + j + b + N0 + d) * p ^ k1 by ring]
          _ = p ^ (2 + j + b + N0 + d) • (p ^ (k1 + n + m1) • (⇑E.nVarpi)^[i] y) := by rw [hr1]
          _ = p ^ (b + N0 + d + k1 + n + m1) • (p ^ (2 + j) • (⇑E.nVarpi)^[i] y) := by
                  rw [smul_smul, smul_smul, show p ^ (2 + j + b + N0 + d) * p ^ (k1 + n + m1) = p ^ (b + N0 + d + k1 + n + m1) * p ^ (2 + j) by ring]
          _ = p ^ (b + N0 + d + k1 + n + m1) • (p ^ 2 • (⇑(nu E))^[2 * j] ((⇑E.nVarpi)^[i] y)) := by rw [hkey]
          _ = (⇑(nu E))^[2 * j] (p ^ (b + N0 + d + k1 + n + m1 + 2) • (⇑E.nVarpi)^[i] y) := by
                  rw [iterate_map_nsmul, smul_smul, ← pow_add]
      have step2 := congrArg ((⇑(nuF E hVF))^[2 * j]) step
      rw [nuF_iterate_nu_iterate, nuF_iterate_nu_iterate, smul_smul, smul_smul, ← pow_add, ← pow_add] at step2
      rw [step2, show 2 * j + (b + N0 + d + k1 + n + m1 + 2) = 2 * j + (2 + j + k1 + a) + n' + (m1 + N0) by omega]

end Core

end LE6

open LE6 CerednikDrinfeld.GradedCartierModuleData MvFormalGroup MvFormalGroup.CartierModule

theorem transfer
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0) (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
    {B : Type} [CommRing B] [Algebra ℤ_[p] B]
    (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)) (m : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p])
    (A : Matrix (Fin 2) (Fin 2) ℤ_[p]) (hA : (p : ℚ_[p]) ^ m • (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) = A.map ((↑) : ℤ_[p] → ℚ_[p]))
    (t : Rigidified p Φ B) (n' : ℕ) (ρ' : Series (B ⧸ pIdeal p B)) (j : ℕ)
    (hOD : FormalODModule.IsODHom (t.Φbar ψ) t.Xbar t.ρ)
    (hOD' : FormalODModule.IsODHom (({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B).Φbar (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j)))) t.Xbar ρ')
    (c0 : ℕ)
    (hG4 : ∀ {S : Type} [CommRing S] (f : B →+* S)
      (hcb : t.IsGradedSbar ι ψ f)
      (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ f) (hcΦf' : Rigidified.IsGradedPhiS (Φ := Φ) ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j))) f)
      (NV : ((t.XbarS f).toGradedCartierModuleData (Rigidified.jSbar ι ψ f) hcb).NMod →+ ((t.XbarS f).toGradedCartierModuleData (Rigidified.jSbar ι ψ f) hcb).NMod)
      (hNV : ∀ x : MvFormalGroup.CartierModule p (t.XbarS f).F × MvFormalGroup.CartierModule p (t.XbarS f).F,
        NV (((t.XbarS f).toGradedCartierModuleData (Rigidified.jSbar ι ψ f) hcb).nMk x) = ((t.XbarS f).toGradedCartierModuleData (Rigidified.jSbar ι ψ f) hcb).nMk ((MvFormalGroup.CartierModule.verschiebungInt)^[2 * j] x.1,
          (MvFormalGroup.CartierModule.verschiebungInt)^[2 * j] x.2))
      (w : Fin 2 → ℤ_[p]),
      p ^ (c0 + t.n + m) • NV (((Rigidified.PhibarS (Φ := Φ) (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j))) f).toGradedCartierModuleData (Rigidified.jPhiS ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j))) f) hcΦf').nMap ((t.XbarS f).toGradedCartierModuleData (Rigidified.jSbar ι ψ f) hcb)
            (Rigidified.rhoC (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j))) ({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B) hOD'.1 f)
            (Rigidified.rhoC_verschiebungInt (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j))) ({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B) hOD'.1 f)
            (Rigidified.rhoC_endAct_varpiEnd (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j))) ({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B) hOD' f)
          ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMap ((Rigidified.PhibarS (Φ := Φ) (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j))) f).toGradedCartierModuleData (Rigidified.jPhiS ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j))) f) hcΦf')
            (Rigidified.bcPhi (Φ := Φ) (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j))) f) (Rigidified.bcPhi_verschiebungInt (Φ := Φ) (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j))) f)
            (Rigidified.bcPhi_endAct_varpiEnd (Φ := Φ) (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j))) f) (rΦ w))) =
        p ^ (c0 + n') • t.rigidNum ι hcΦ rΦ ψ hOD f hcb hcΦf (A.mulVec w))
    (c : ℚ_[p]ˣ) (hc : (c : ℚ_[p]) = (p : ℚ_[p]) ^ j)
    (i : Fin 2) (v : Fin 2 → ℚ_[p]) (f : B)
    (hc' : t.IsGradedS ι ψ (Rigidified.awayHom f)) (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f))
    (hcΦ' : Rigidified.IsGradedPhiS (Φ := Φ) ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j))) (Rigidified.awayHom f))
    (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
    (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc').IsCanonicalLMap L)
    (z : _) (hz : z ∈ ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc').etaPiece L
      hL.isCartierLMap.map_verschiebung i) :
    Rigidified.LatticeRel ((t.XbarS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom f)) hcb) n'
        ((((Rigidified.PhibarS (Φ := Φ) (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j))) (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jPhiS ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j))) (Rigidified.awayHom f)) hcΦ').nMap
            ((t.XbarS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom f)) hcb)
            (Rigidified.rhoC (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j))) ({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B) hOD'.1 (Rigidified.awayHom f))
            (Rigidified.rhoC_verschiebungInt (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j))) ({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B) hOD'.1 (Rigidified.awayHom f))
            (Rigidified.rhoC_endAct_varpiEnd (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j))) ({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B) hOD' (Rigidified.awayHom f))).comp
          (((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMap
              ((Rigidified.PhibarS (Φ := Φ) (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j))) (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jPhiS ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j))) (Rigidified.awayHom f)) hcΦ')
              (Rigidified.bcPhi (Φ := Φ) (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j))) (Rigidified.awayHom f)) (Rigidified.bcPhi_verschiebungInt (Φ := Φ) (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j))) (Rigidified.awayHom f))
              (Rigidified.bcPhi_endAct_varpiEnd (Φ := Φ) (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j))) (Rigidified.awayHom f))).comp rΦ))
        (((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc').nMap
          ((t.XbarS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom f)) hcb)
          (t.redC (Rigidified.awayHom f)) (t.redC_verschiebungInt (Rigidified.awayHom f)) (t.redC_endAct_varpiEnd (Rigidified.awayHom f))
          (((((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc').nVarpi :
              _ →ₗ[WittVector p (Rigidified.Baway f)] _) ^ (i : ℕ)) z))
        ((p : ℚ_[p]) ^ (i : ℕ) • v) ↔
      Rigidified.LatticeRel ((t.XbarS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom f)) hcb) t.n
        (t.rigidNum ι hcΦ rΦ ψ hOD (Rigidified.awayHom f) hcb hcΦf)
        (t.etaRed ι ψ (Rigidified.awayHom f) hc' hcb
          (((((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc').nVarpi :
              _ →ₗ[WittVector p (Rigidified.Baway f)] _) ^ (i : ℕ)) z))
        ((p : ℚ_[p]) ^ (i : ℕ) • (((c⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) • ((g : Matrix (Fin 2) (Fin 2) ℚ_[p]) *ᵥ v))) := by

  let S := Rigidified.Baway f
  let gS : B →+* S := Rigidified.awayHom f
  let D := (t.XS gS).toGradedCartierModuleData (Rigidified.jS ι ψ gS) hc'
  let E := (t.XbarS gS).toGradedCartierModuleData (Rigidified.jSbar ι ψ gS) hcb
  have hS : IsNilpotent ((p : ℕ) : S) := by
    obtain ⟨N, hN⟩ := hB
    exact ⟨N, by rw [← map_natCast gS p, ← map_pow, hN, map_zero]⟩
  have hp0 : ((p : ℕ) : S ⧸ pIdeal p S) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk (pIdeal p S))]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have hVF : ∀ x : E.M, E.verschiebung (E.frobenius x) = (p : ℕ) • x :=
    verschiebung_frobenius_eq_nsmul E hp0

  obtain ⟨Lb, hLb⟩ := exists_isCanonicalLMap_bar ι ψ t gS hc' hcb L hL
  have hredF : ∀ x, t.redC gS (D.frobenius x) = E.frobenius (t.redC gS x) := fun x =>
    baseChangeEq_frobenius _ (t.XS_F_map_mk gS) x
  have hy : (p : ℕ) • t.etaRed ι ψ gS hc' hcb z ∈ E.eta Lb hLb.isCartierLMap.map_verschiebung :=
    CerednikDrinfeld.GradedCartierModuleData.nsmul_nMap_mem_eta_of_mem_eta_of_cast_eq_zero p hp0 D E (t.redC gS)
      hredF (t.redC_verschiebungInt gS) (t.redC_endAct_varpiEnd gS) L hL.isCartierLMap Lb hLb.isCartierLMap z
      (AddSubgroup.mem_inf.mp hz).1

  let NV : E.NMod →+ E.NMod := AddMonoidHom.mk' (fun z => (⇑(nu E))^[2 * j] z) (iterate_map_add (nu E) (2 * j))
  have hNV : ∀ x : MvFormalGroup.CartierModule p (t.XbarS gS).F × MvFormalGroup.CartierModule p (t.XbarS gS).F,
      NV (E.nMk x) =
        E.nMk ((MvFormalGroup.CartierModule.verschiebungInt)^[2 * j] x.1, (MvFormalGroup.CartierModule.verschiebungInt)^[2 * j] x.2) := by
    rintro ⟨a, b⟩
    exact nu_iterate_nMk E (2 * j) a b
  have hG4' : ∀ w : Fin 2 → ℤ_[p],
      p ^ (c0 + t.n + m) • (⇑(nu E))^[2 * j]
        (((((Rigidified.PhibarS (Φ := Φ) (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j))) gS).toGradedCartierModuleData (Rigidified.jPhiS ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j))) gS) hcΦ').nMap E
            (Rigidified.rhoC (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j))) ({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B) hOD'.1 gS)
            (Rigidified.rhoC_verschiebungInt (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j))) ({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B) hOD'.1 gS)
            (Rigidified.rhoC_endAct_varpiEnd (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j))) ({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B) hOD' gS)).comp
          (((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMap
              ((Rigidified.PhibarS (Φ := Φ) (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j))) gS).toGradedCartierModuleData (Rigidified.jPhiS ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j))) gS) hcΦ')
              (Rigidified.bcPhi (Φ := Φ) (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j))) gS) (Rigidified.bcPhi_verschiebungInt (Φ := Φ) (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j))) gS)
              (Rigidified.bcPhi_endAct_varpiEnd (Φ := Φ) (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j))) gS)).comp rΦ)) w) =
      p ^ (c0 + n') • t.rigidNum ι hcΦ rΦ ψ hOD gS hcb hcΦf (A *ᵥ w) := by
    intro w
    exact hG4 gS hcb hcΦf hcΦ' NV hNV w

  have hp0Q : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hcinv : ((c⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) = ((p : ℚ_[p]) ^ j)⁻¹ := by rw [Units.val_inv_eq_inv_val, hc]
  have hAVU : (A.map ((↑) : ℤ_[p] → ℚ_[p])) *ᵥ ((p : ℚ_[p]) ^ (i : ℕ) • v) =
      (p : ℚ_[p]) ^ (m + j) • ((p : ℚ_[p]) ^ (i : ℕ) • (((c⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) • ((g : Matrix (Fin 2) (Fin 2) ℚ_[p]) *ᵥ v))) := by
    rw [← hA, Matrix.mulVec_smul, Matrix.smul_mulVec, smul_smul, smul_smul, smul_smul, hcinv]
    congr 1
    rw [pow_add]
    field_simp

  have key := core E hVF Lb hLb.isCartierLMap (t.etaRed ι ψ gS hc' hcb z) hy (i : ℕ)
    (t.rigidNum ι hcΦ rΦ ψ hOD gS hcb hcΦf) _ A j (c0 + t.n + m) (c0 + n') (m + j) t.n n' (by omega) hG4' _ _ hAVU
  rw [nMap_nVarpi_pow, Rigidified.etaRed, nMap_nVarpi_pow]
  exact key

namespace B32TE

open CerednikDrinfeld.FormalODModule MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld.SpecialFormal.Rigidified

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O]

section
variable (ι : Zp2 p →+* O) {Φ : FormalODModule p (O ⧸ pIdeal p O)}
  (hcΦ : IsCompl (Φ.gradedPiece (Rigidified.jbar ι) 0) (Φ.gradedPiece (Rigidified.jbar ι) 1))
  (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
  {B : Type} [CommRing B]

def ES (ψ : O →+* B) (t : Rigidified p Φ B) (hOD : IsODHom (t.Φbar ψ) t.Xbar t.ρ)
    {S : Type} [CommRing S] (g : B →+* S) (jB : Zp2 p →+* B)
    (hc : IsCompl ((t.XS g).gradedPiece (g.comp jB) 0) ((t.XS g).gradedPiece (g.comp jB) 1))
    (hcb : IsCompl ((t.XbarS g).gradedPiece ((reduceMap g).comp ((Ideal.Quotient.mk (pIdeal p B)).comp jB)) 0)
      ((t.XbarS g).gradedPiece ((reduceMap g).comp ((Ideal.Quotient.mk (pIdeal p B)).comp jB)) 1))
    (hcΦg : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ g)
    (L : ((t.XS g).toGradedCartierModuleData (g.comp jB) hc).M →+
      ((t.XS g).toGradedCartierModuleData (g.comp jB) hc).NMod)
    (hL : ((t.XS g).toGradedCartierModuleData (g.comp jB) hc).IsCanonicalLMap L)
    (i : Fin 2) (z : ((t.XS g).toGradedCartierModuleData (g.comp jB) hc).NMod)
    (v : Fin 2 → ℚ_[p]) : Prop :=
  let D := (t.XS g).toGradedCartierModuleData (g.comp jB) hc
  z ∈ D.etaPiece L hL.isCartierLMap.map_verschiebung i ∧
    Rigidified.LatticeRel ((t.XbarS g).toGradedCartierModuleData
        ((reduceMap g).comp ((Ideal.Quotient.mk (pIdeal p B)).comp jB)) hcb) t.n
      ((((Rigidified.PhibarS (Φ := Φ) ψ g).toGradedCartierModuleData (Rigidified.jPhiS ι ψ g) hcΦg).nMap
          ((t.XbarS g).toGradedCartierModuleData ((reduceMap g).comp ((Ideal.Quotient.mk (pIdeal p B)).comp jB)) hcb)
          (Rigidified.rhoC ψ t hOD.1 g) (Rigidified.rhoC_verschiebungInt ψ t hOD.1 g)
          (Rigidified.rhoC_endAct_varpiEnd ψ t hOD g)).comp
        (((Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).nMap
            ((Rigidified.PhibarS (Φ := Φ) ψ g).toGradedCartierModuleData (Rigidified.jPhiS ι ψ g) hcΦg)
            (Rigidified.bcPhi (Φ := Φ) ψ g) (Rigidified.bcPhi_verschiebungInt (Φ := Φ) ψ g)
            (Rigidified.bcPhi_endAct_varpiEnd (Φ := Φ) ψ g)).comp rΦ))
      ((D.nMap
        ((t.XbarS g).toGradedCartierModuleData ((reduceMap g).comp ((Ideal.Quotient.mk (pIdeal p B)).comp jB)) hcb)
        (t.redC g) (t.redC_verschiebungInt g) (t.redC_endAct_varpiEnd g))
        (((D.nVarpi : D.NMod →ₗ[WittVector p S] D.NMod) ^ (i : ℕ)) z))
      ((p : ℚ_[p]) ^ (i : ℕ) • v)

def ICQ [Algebra ℤ_[p] B] (ψ : O →+* B) (t : Rigidified p Φ B) (jB : Zp2 p →+* B)
    (Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B) : Prop :=
  IsODHom (t.Φbar ψ) t.Xbar t.ρ ∧
  ∃ (τ₀ : Q.T₀ ≃ₗ[B] ↥(t.X.lieZero jB))
    (τ₁ : Q.T₁ ≃ₗ[B] ↥(t.X.lieOne jB)),
    (∀ s : Q.T₀, ((τ₁ (Q.Pi₀ s) : ↥(t.X.lieOne jB)) : t.X.Lie) =
        t.X.lieVarpi ((τ₀ s : ↥(t.X.lieZero jB)) : t.X.Lie)) ∧
    (∀ s : Q.T₁, ((τ₀ (Q.Pi₁ s) : ↥(t.X.lieZero jB)) : t.X.Lie) =
        t.X.lieVarpi ((τ₁ s : ↥(t.X.lieOne jB)) : t.X.Lie)) ∧
    ∀ (hOD : IsODHom (t.Φbar ψ) t.Xbar t.ρ) (x : PrimeSpectrum B),
      (∀ v, v ∈ Q.N₀ x ↔
        ∃ (f : B) (_ : f ∉ x.asIdeal)
          (hc : IsCompl ((t.XS (awayHom f)).gradedPiece ((awayHom f).comp jB) 0) ((t.XS (awayHom f)).gradedPiece ((awayHom f).comp jB) 1))
          (hcb : IsCompl ((t.XbarS (awayHom f)).gradedPiece ((reduceMap (awayHom f)).comp ((Ideal.Quotient.mk (pIdeal p B)).comp jB)) 0)
            ((t.XbarS (awayHom f)).gradedPiece ((reduceMap (awayHom f)).comp ((Ideal.Quotient.mk (pIdeal p B)).comp jB)) 1))
          (hcΦf : IsGradedPhiS (Φ := Φ) ι ψ (awayHom f))
          (L : _) (hL : ((t.XS (awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L),
          ∃ z, ES ι hcΦ rΦ ψ t hOD (awayHom f) jB hc hcb hcΦf L hL 0 z v) ∧
      (∀ v, v ∈ Q.N₁ x ↔
        ∃ (f : B) (_ : f ∉ x.asIdeal)
          (hc : IsCompl ((t.XS (awayHom f)).gradedPiece ((awayHom f).comp jB) 0) ((t.XS (awayHom f)).gradedPiece ((awayHom f).comp jB) 1))
          (hcb : IsCompl ((t.XbarS (awayHom f)).gradedPiece ((reduceMap (awayHom f)).comp ((Ideal.Quotient.mk (pIdeal p B)).comp jB)) 0)
            ((t.XbarS (awayHom f)).gradedPiece ((reduceMap (awayHom f)).comp ((Ideal.Quotient.mk (pIdeal p B)).comp jB)) 1))
          (hcΦf : IsGradedPhiS (Φ := Φ) ι ψ (awayHom f))
          (L : _) (hL : ((t.XS (awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L),
          ∃ z, ES ι hcΦ rΦ ψ t hOD (awayHom f) jB hc hcb hcΦf L hL 1 z v) ∧
      (∀ (v : Fin 2 → ℚ_[p]) (hv : v ∈ Q.N₀ x) (f : B) (hf : f ∉ x.asIdeal)
          (hc : IsCompl ((t.XS (awayHom f)).gradedPiece ((awayHom f).comp jB) 0) ((t.XS (awayHom f)).gradedPiece ((awayHom f).comp jB) 1))
          (hcb : IsCompl ((t.XbarS (awayHom f)).gradedPiece ((reduceMap (awayHom f)).comp ((Ideal.Quotient.mk (pIdeal p B)).comp jB)) 0)
            ((t.XbarS (awayHom f)).gradedPiece ((reduceMap (awayHom f)).comp ((Ideal.Quotient.mk (pIdeal p B)).comp jB)) 1))
          (hcΦf : IsGradedPhiS (Φ := Φ) ι ψ (awayHom f))
          (L : _) (hL : ((t.XS (awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L)
          (z : _) (hz : ES ι hcΦ rΦ ψ t hOD (awayHom f) jB hc hcb hcΦf L hL 0 z v),
        ∃ (m : ((t.XS (awayHom f)).toGradedCartierModuleData _ hc).M) (s : Q.T₀)
          (b : x.asIdeal.primeCompl),
          ((t.XS (awayHom f)).toGradedCartierModuleData _ hc).vRange.mkQ m =
            ((t.XS (awayHom f)).toGradedCartierModuleData _ hc).u L
              hL.isCartierLMap.map_verschiebung ⟨z, (AddSubgroup.mem_inf.mp hz.1).1⟩ ∧
          Q.u₀ x ((1 : Bloc x) ⊗ₜ[ℤ_[p]] (⟨v, hv⟩ : ↥(Q.N₀ x))) = LocalizedModule.mk s b ∧
          ∀ i, locHom x ((τ₀ s : t.X.Lie) i) =
            locHom x (b : B) * awayToLoc x f hf (tangent m i)) ∧
      (∀ (v : Fin 2 → ℚ_[p]) (hv : v ∈ Q.N₁ x) (f : B) (hf : f ∉ x.asIdeal)
          (hc : IsCompl ((t.XS (awayHom f)).gradedPiece ((awayHom f).comp jB) 0) ((t.XS (awayHom f)).gradedPiece ((awayHom f).comp jB) 1))
          (hcb : IsCompl ((t.XbarS (awayHom f)).gradedPiece ((reduceMap (awayHom f)).comp ((Ideal.Quotient.mk (pIdeal p B)).comp jB)) 0)
            ((t.XbarS (awayHom f)).gradedPiece ((reduceMap (awayHom f)).comp ((Ideal.Quotient.mk (pIdeal p B)).comp jB)) 1))
          (hcΦf : IsGradedPhiS (Φ := Φ) ι ψ (awayHom f))
          (L : _) (hL : ((t.XS (awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L)
          (z : _) (hz : ES ι hcΦ rΦ ψ t hOD (awayHom f) jB hc hcb hcΦf L hL 1 z v),
        ∃ (m : ((t.XS (awayHom f)).toGradedCartierModuleData _ hc).M) (s : Q.T₁)
          (b : x.asIdeal.primeCompl),
          ((t.XS (awayHom f)).toGradedCartierModuleData _ hc).vRange.mkQ m =
            ((t.XS (awayHom f)).toGradedCartierModuleData _ hc).u L
              hL.isCartierLMap.map_verschiebung ⟨z, (AddSubgroup.mem_inf.mp hz.1).1⟩ ∧
          Q.u₁ x ((1 : Bloc x) ⊗ₜ[ℤ_[p]] (⟨v, hv⟩ : ↥(Q.N₁ x))) = LocalizedModule.mk s b ∧
          ∀ i, locHom x ((τ₁ s : t.X.Lie) i) =
            locHom x (b : B) * awayToLoc x f hf (tangent m i))

theorem isCartierQuadruple_iff_ICQ [Algebra ℤ_[p] B] (ψ : O →+* B) (t : Rigidified p Φ B)
    (jB : Zp2 p →+* B) (hjB : structureMap ι ψ = jB) (Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B) :
    t.IsCartierQuadruple ι hcΦ rΦ ψ Q ↔ ICQ ι hcΦ rΦ ψ t jB Q := by
  subst hjB
  exact Iff.rfl

end

end B32TE

open B32TE LE6 CerednikDrinfeld.GradedCartierModuleData MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld.SpecialFormal.Rigidified in

theorem solution
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι)) (hΦ4 : Φ.HasHeight 4)
    (hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0) (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
    (hrΦ : ∀ (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
      (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L),
      Set.BijOn rΦ Set.univ ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung 0 : Set _))
    {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B]
    (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B))
    (E : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) ℚ_[p]) (m : ℕ)
    (hEinj : Function.Injective E)
    (hEord : ∀ e, ∃ A : Matrix (Fin 2) (Fin 2) ℤ_[p], (p : ℚ_[p]) ^ m • E e = A.map ((↑) : ℤ_[p] → ℚ_[p]))
    (hEcompat : (∀ (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (A : Matrix (Fin 2) (Fin 2) ℤ_[p]),
        (p : ℚ_[p]) ^ m • E e = A.map ((↑) : ℤ_[p] → ℚ_[p]) →
        ∀ (Ne : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod),
          (∀ x : MvFormalGroup.CartierModule p Φ.F × (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).Sigma,
            Ne ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk x) =
              (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk
                (MvFormalGroup.CartierModule.endAct (e : MvFormalGroup.End Φ.F) x.1,
                 (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).toSigma
                   (MvFormalGroup.CartierModule.endAct (e : MvFormalGroup.End Φ.F)
                     ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).ofSigma x.2)))) →
          ∀ w : Fin 2 → ℤ_[p], p ^ m • Ne (rΦ w) = rΦ (A.mulVec w)))
    (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (m' : ℕ)
    (hker : FormalODModule.HasKernelOfDegree (e : MvFormalGroup.End Φ.F).toPowerSeries (p ^ (2 * m')))
    (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p]) (hg : (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) = E e)
    (t t' : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ)
    (ht' : t'.IsAdmissible ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')))
    (htr : Rigidified.IsTranslate (e : MvFormalGroup.End Φ.F).toPowerSeries 0 m' ψ t t')
    (Q Q' : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B)
    (hQ : t.IsCartierQuadruple ι hcΦ rΦ ψ Q)
    (hQ' : t'.IsCartierQuadruple ι hcΦ rΦ (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) Q')
    (j : ℕ) (hm' : m' = 2 * j) (c : ℚ_[p]ˣ) (hc : (c : ℚ_[p]) = (p : ℚ_[p]) ^ j) :
    ∃ (τ₀ : Q.T₀ ≃ₗ[B] Q'.T₀) (τ₁ : Q.T₁ ≃ₗ[B] Q'.T₁),
      (∀ s, τ₁ (Q.Pi₀ s) = Q'.Pi₀ (τ₀ s)) ∧ (∀ s, τ₀ (Q.Pi₁ s) = Q'.Pi₁ (τ₁ s)) ∧
      (∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]) (hv : v ∈ Q.N₀ x)
        (hv' : ((scalarGL c * g⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]).mulVec v ∈ Q'.N₀ x),
        Q'.u₀ x ((1 : locRing B x) ⊗ₜ[ℤ_[p]] (⟨_, hv'⟩ : ↥(Q'.N₀ x))) =
          LocalizedModule.map x.asIdeal.primeCompl τ₀.toLinearMap
            (Q.u₀ x ((1 : locRing B x) ⊗ₜ[ℤ_[p]] (⟨v, hv⟩ : ↥(Q.N₀ x))))) ∧
      (∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]) (hv : v ∈ Q.N₁ x)
        (hv' : ((scalarGL c * g⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]).mulVec v ∈ Q'.N₁ x),
        Q'.u₁ x ((1 : locRing B x) ⊗ₜ[ℤ_[p]] (⟨_, hv'⟩ : ↥(Q'.N₁ x))) =
          LocalizedModule.map x.asIdeal.primeCompl τ₁.toLinearMap
            (Q.u₁ x ((1 : locRing B x) ⊗ₜ[ℤ_[p]] (⟨v, hv⟩ : ↥(Q.N₁ x))))) := by
  classical

  obtain ⟨X', n', ρ'⟩ := t'
  have hX : X' = t.X := htr.1
  subst hX
  subst hm'
  haveI : ExpChar k p := ExpChar.prime (Fact.out : p.Prime)

  have hsm : structureMap ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j))) = structureMap ι ψ :=
    B28SM.structureMap_comp_frobenius_pow_two_mul k ι ψ j

  obtain ⟨A, hA⟩ := hEord e
  obtain ⟨c0, hG4⟩ :=
    CerednikDrinfeld.SpecialFormal.Rigidified.exists_nsmul_nMap_rigidNum_translate_eq_nsmul_rigidNum_mulVec p k ι Φ hΦ hΦ4 hcΦ
      rΦ hrΦ ψ hB E m hEinj hEord hEcompat e (2 * j) hker g hg A hA t ht n' ρ' ht' htr
  have hA' : (p : ℚ_[p]) ^ m • (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) = A.map ((↑) : ℤ_[p] → ℚ_[p]) := by rw [hg]; exact hA

  have hOD := hQ.1
  have hQ'' := (B32TE.isCartierQuadruple_iff_ICQ ι hcΦ rΦ
    (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j)))
    ({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B) (structureMap ι ψ) hsm Q').mp hQ'
  have hOD' := hQ''.1
  obtain ⟨τQ₀, τQ₁, hT0, hT1, hN⟩ := hQ.2
  obtain ⟨τQ₀', τQ₁', hT0', hT1', hN'⟩ := hQ''.2
  have hp1 : ∀ f : B, IsNilpotent ((p : ℕ) : Rigidified.Baway f ⧸ pIdeal p (Rigidified.Baway f)) := fun f =>
    ⟨1, by rw [pow_one, ← map_natCast (Ideal.Quotient.mk (pIdeal p (Rigidified.Baway f)))]
           exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))⟩

  set Mx : Matrix (Fin 2) (Fin 2) ℚ_[p] := ((scalarGL c * g⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) with hMx
  have hMv : ∀ v : Fin 2 → ℚ_[p], ((c⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) • ((g : Matrix (Fin 2) (Fin 2) ℚ_[p]) *ᵥ (Mx *ᵥ v)) = v := by
    intro v
    rw [← inv_scalarGL_mul_inv_mulVec c g, hMx, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]
  refine ⟨τQ₀.trans τQ₀'.symm, τQ₁.trans τQ₁'.symm, ?_, ?_, ?_, ?_⟩
  · intro s
    apply τQ₁'.injective
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [hT0, hT0', LinearEquiv.apply_symm_apply]
  · intro s
    apply τQ₀'.injective
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [hT1, hT1', LinearEquiv.apply_symm_apply]
  ·
    intro x v hv hv'
    obtain ⟨hN0, hN1, hu0, hu1⟩ := hN hOD x
    obtain ⟨hN0', hN1', hu0', hu1'⟩ := hN' hOD' x
    obtain ⟨f, hf, hcS, hcb, hcΦf, L, hL, z, hz⟩ := (hN0 v).mp hv
    have hcΦf' : Rigidified.IsGradedPhiS (Φ := Φ) ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j))) (Rigidified.awayHom f) :=
      CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent p _ (hp1 f) _
    have hz' : B32TE.ES ι hcΦ rΦ (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j)))
        ({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B) hOD' (Rigidified.awayHom f) (structureMap ι ψ) hcS hcb hcΦf' L hL 0 z (Mx *ᵥ v) := by
      refine ⟨hz.1, ?_⟩
      refine (transfer p k ι Φ hcΦ rΦ ψ hB m g A hA' t n' ρ' j hOD hOD' c0 (fun f' hcb₁ hcΦ₁ hcΦ₂ NV hNV w => hG4 hOD hOD' f' hcb₁ hcΦ₁ hcΦ₂ NV hNV w) c hc 0 (Mx *ᵥ v) f hcS hcb hcΦf' hcΦf L hL z hz.1).mpr ?_
      rw [hMv]
      exact hz.2
    obtain ⟨m₁, s₁, b₁, hmu₁, hQu₁, htan₁⟩ := hu0 v hv f hf hcS hcb hcΦf L hL z hz
    obtain ⟨m₂, s₂, b₂, hmu₂, hQu₂, htan₂⟩ := hu0' (Mx *ᵥ v) hv' f hf hcS hcb hcΦf' L hL z hz'

    have hmm : m₁ - m₂ ∈ ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hcS).vRange := by
      rw [← Submodule.Quotient.eq, ← Submodule.mkQ_apply, ← Submodule.mkQ_apply]
      exact hmu₁.trans hmu₂.symm
    obtain ⟨y, hy⟩ := hmm
    have htan : tangent m₁ = tangent m₂ := by
      have h0 : tangent (m₁ - m₂) = 0 := by
        rw [← hy]; exact tangent_verschiebungInt y
      have h1 := AddMonoidHom.map_sub (tangent (p := p) (Φ := (t.XS (Rigidified.awayHom f)).F)) m₁ m₂
      exact sub_eq_zero.mp (h1.symm.trans h0)

    have key : ∀ i : Fin 2, ∃ u : x.asIdeal.primeCompl,
        (u : B) * ((b₂ : B) * (τQ₀ s₁ : t.X.Lie) i) = (u : B) * ((b₁ : B) * (τQ₀' s₂ : t.X.Lie) i) := by
      intro i
      apply (IsLocalization.eq_iff_exists x.asIdeal.primeCompl (Rigidified.Bloc x)).mp
      show Rigidified.locHom x _ = Rigidified.locHom x _
      rw [map_mul, map_mul, htan₁ i, htan₂ i, htan]
      ring
    obtain ⟨u₀, hu₀⟩ := key 0
    obtain ⟨w₁, hw₁⟩ := key 1
    have hvec : (((u₀ : B) * (w₁ : B)) * (b₂ : B)) • (τQ₀ s₁ : t.X.Lie) =
        (((u₀ : B) * (w₁ : B)) * (b₁ : B)) • (τQ₀' s₂ : t.X.Lie) := by
      refine funext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
      · simp only [Pi.smul_apply, smul_eq_mul]
        linear_combination (w₁ : B) * hu₀
      · simp only [Pi.smul_apply, smul_eq_mul]
        linear_combination (u₀ : B) * hw₁
    have hsub : (((u₀ : B) * (w₁ : B)) * (b₂ : B)) • τQ₀ s₁ = (((u₀ : B) * (w₁ : B)) * (b₁ : B)) • τQ₀' s₂ := by
      apply Subtype.ext
      rw [Submodule.coe_smul, Submodule.coe_smul]
      exact hvec
    have hT : (((u₀ : B) * (w₁ : B)) * (b₂ : B)) • τQ₀'.symm (τQ₀ s₁) = (((u₀ : B) * (w₁ : B)) * (b₁ : B)) • s₂ := by
      apply τQ₀'.injective
      rw [map_smul, map_smul, LinearEquiv.apply_symm_apply]
      exact hsub
    rw [hQu₂, hQu₁, LocalizedModule.map_mk, LocalizedModule.mk_eq]
    refine ⟨u₀ * w₁, ?_⟩
    simp only [Submonoid.smul_def, Submonoid.coe_mul, LinearEquiv.coe_coe, LinearEquiv.trans_apply, smul_smul]
    exact hT.symm
  ·
    intro x v hv hv'
    obtain ⟨hN0, hN1, hu0, hu1⟩ := hN hOD x
    obtain ⟨hN0', hN1', hu0', hu1'⟩ := hN' hOD' x
    obtain ⟨f, hf, hcS, hcb, hcΦf, L, hL, z, hz⟩ := (hN1 v).mp hv
    have hcΦf' : Rigidified.IsGradedPhiS (Φ := Φ) ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j))) (Rigidified.awayHom f) :=
      CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent p _ (hp1 f) _
    have hz' : B32TE.ES ι hcΦ rΦ (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j)))
        ({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B) hOD' (Rigidified.awayHom f) (structureMap ι ψ) hcS hcb hcΦf' L hL 1 z (Mx *ᵥ v) := by
      refine ⟨hz.1, ?_⟩
      refine (transfer p k ι Φ hcΦ rΦ ψ hB m g A hA' t n' ρ' j hOD hOD' c0 (fun f' hcb₁ hcΦ₁ hcΦ₂ NV hNV w => hG4 hOD hOD' f' hcb₁ hcΦ₁ hcΦ₂ NV hNV w) c hc 1 (Mx *ᵥ v) f hcS hcb hcΦf' hcΦf L hL z hz.1).mpr ?_
      rw [hMv]
      exact hz.2
    obtain ⟨m₁, s₁, b₁, hmu₁, hQu₁, htan₁⟩ := hu1 v hv f hf hcS hcb hcΦf L hL z hz
    obtain ⟨m₂, s₂, b₂, hmu₂, hQu₂, htan₂⟩ := hu1' (Mx *ᵥ v) hv' f hf hcS hcb hcΦf' L hL z hz'

    have hmm : m₁ - m₂ ∈ ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hcS).vRange := by
      rw [← Submodule.Quotient.eq, ← Submodule.mkQ_apply, ← Submodule.mkQ_apply]
      exact hmu₁.trans hmu₂.symm
    obtain ⟨y, hy⟩ := hmm
    have htan : tangent m₁ = tangent m₂ := by
      have h0 : tangent (m₁ - m₂) = 0 := by
        rw [← hy]; exact tangent_verschiebungInt y
      have h1 := AddMonoidHom.map_sub (tangent (p := p) (Φ := (t.XS (Rigidified.awayHom f)).F)) m₁ m₂
      exact sub_eq_zero.mp (h1.symm.trans h0)

    have key : ∀ i : Fin 2, ∃ u : x.asIdeal.primeCompl,
        (u : B) * ((b₂ : B) * (τQ₁ s₁ : t.X.Lie) i) = (u : B) * ((b₁ : B) * (τQ₁' s₂ : t.X.Lie) i) := by
      intro i
      apply (IsLocalization.eq_iff_exists x.asIdeal.primeCompl (Rigidified.Bloc x)).mp
      show Rigidified.locHom x _ = Rigidified.locHom x _
      rw [map_mul, map_mul, htan₁ i, htan₂ i, htan]
      ring
    obtain ⟨u₀, hu₀⟩ := key 0
    obtain ⟨w₁, hw₁⟩ := key 1
    have hvec : (((u₀ : B) * (w₁ : B)) * (b₂ : B)) • (τQ₁ s₁ : t.X.Lie) =
        (((u₀ : B) * (w₁ : B)) * (b₁ : B)) • (τQ₁' s₂ : t.X.Lie) := by
      refine funext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
      · simp only [Pi.smul_apply, smul_eq_mul]
        linear_combination (w₁ : B) * hu₀
      · simp only [Pi.smul_apply, smul_eq_mul]
        linear_combination (u₀ : B) * hw₁
    have hsub : (((u₀ : B) * (w₁ : B)) * (b₂ : B)) • τQ₁ s₁ = (((u₀ : B) * (w₁ : B)) * (b₁ : B)) • τQ₁' s₂ := by
      apply Subtype.ext
      rw [Submodule.coe_smul, Submodule.coe_smul]
      exact hvec
    have hT : (((u₀ : B) * (w₁ : B)) * (b₂ : B)) • τQ₁'.symm (τQ₁ s₁) = (((u₀ : B) * (w₁ : B)) * (b₁ : B)) • s₂ := by
      apply τQ₁'.injective
      rw [map_smul, map_smul, LinearEquiv.apply_symm_apply]
      exact hsub
    rw [hQu₂, hQu₁, LocalizedModule.map_mk, LocalizedModule.mk_eq]
    refine ⟨u₀ * w₁, ?_⟩
    simp only [Submonoid.smul_def, Submonoid.coe_mul, LinearEquiv.coe_coe, LinearEquiv.trans_apply, smul_smul]
    exact hT.symm

end S_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_exists_linearEquiv_stalkMap_comp_of_isTranslate_of_even
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_exists_linearEquiv_stalkMap_comp_of_isTranslate_of_even (solution)
