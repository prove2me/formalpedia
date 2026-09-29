-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.comp_frobenius_of_isPiTranslate
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/e4099354-5ecc-51ff-a1b5-937380ab1bba

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_PeriodMapSpec
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Definitions.Def_CerednikDrinfeld_ODModuleFrobeniusTwist
import Theorems.Thm_WittVector_eq_or_eq_comp_frobenius_of_ringHom_galoisField_two
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isCompl_gradedPiece_zero_one_of_isNilpotent
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isCanonicalLMap_toGradedCartierModuleData_of_isSpecial_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_comp_frobenius_of_isPiTranslate
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega
open scoped PadicInt Padic

namespace ShiftTransfer

open CerednikDrinfeld.FormalODModule CerednikDrinfeld.GradedCartierModuleData MvFormalGroup MvFormalGroup.CartierModule

open MvPowerSeries (subst HasSubst hasSubst_of_constantCoeff_zero constantCoeff)

section Iota

variable {p : ℕ} [hp : Fact p.Prime]

theorem frobenius_comp_ne (k : Type) [Field k] [CharP k p]
    (ι : Zp2 p →+* WittVector p k) :
    (WittVector.frobenius : WittVector p k →+* WittVector p k).comp ι ≠ ι := by
  classical
  intro h

  set θ : Zp2 p →+* k := (WittVector.constantCoeff : WittVector p k →+* k).comp ι with hθ
  have hfix : ∀ x : Zp2 p, θ x ^ p = θ x := by
    intro x
    have hx := congrArg (fun f : Zp2 p →+* WittVector p k => (f x).coeff 0) h
    simp only [RingHom.comp_apply, WittVector.coeff_frobenius_charP] at hx
    exact hx

  haveI : Fintype (GaloisField p 2) := Fintype.ofFinite _
  have hinj : Function.Injective (fun c : GaloisField p 2 => θ (WittVector.teichmuller p c)) := by
    intro c c' hcc
    by_contra hne
    have hunit : IsUnit (WittVector.teichmuller p c - WittVector.teichmuller p c') := by
      apply WittVector.isUnit_of_coeff_zero_ne_zero
      have h0 : (WittVector.teichmuller p c - WittVector.teichmuller p c').coeff 0 = c - c' := by
        show WittVector.constantCoeff (WittVector.teichmuller p c - WittVector.teichmuller p c') = c - c'
        rw [map_sub]
        show (WittVector.teichmuller p c).coeff 0 - (WittVector.teichmuller p c').coeff 0 = c - c'
        rw [WittVector.teichmuller_coeff_zero, WittVector.teichmuller_coeff_zero]
      rw [h0]
      exact sub_ne_zero.mpr hne
    have h0 : θ (WittVector.teichmuller p c - WittVector.teichmuller p c') = 0 := by
      rw [map_sub]; exact sub_eq_zero.mpr hcc
    exact (hunit.map θ).ne_zero h0

  have hroots : ∀ c : GaloisField p 2,
      θ (WittVector.teichmuller p c) ∈ (Polynomial.X ^ p - Polynomial.X : Polynomial k).roots := by
    intro c
    have hne : (Polynomial.X ^ p - Polynomial.X : Polynomial k) ≠ 0 :=
      FiniteField.X_pow_card_sub_X_ne_zero k hp.out.one_lt
    rw [Polynomial.mem_roots hne, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, hfix, sub_self]
  have hcard : Fintype.card (GaloisField p 2) ≤ p := by
    calc Fintype.card (GaloisField p 2)
        = (Finset.univ.image (fun c : GaloisField p 2 => θ (WittVector.teichmuller p c))).card := by
          rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
      _ ≤ (Polynomial.X ^ p - Polynomial.X : Polynomial k).roots.toFinset.card := by
          apply Finset.card_le_card
          intro u hu
          obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hu
          exact Multiset.mem_toFinset.mpr (hroots c)
      _ ≤ (Polynomial.X ^ p - Polynomial.X : Polynomial k).roots.card := Multiset.toFinset_card_le _
      _ ≤ (Polynomial.X ^ p - Polynomial.X : Polynomial k).natDegree := Polynomial.card_roots' _
      _ = p := FiniteField.X_pow_card_sub_X_natDegree_eq k hp.out.one_lt
  have hcard' : Fintype.card (GaloisField p 2) = p ^ 2 := by
    rw [← Nat.card_eq_fintype_card]; exact GaloisField.card p 2 two_ne_zero
  rw [hcard'] at hcard
  have : p < p ^ 2 := by
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ 2 := Nat.pow_lt_pow_right hp.out.one_lt (by norm_num)
  omega

theorem frobenius_comp_eq_comp_frobenius (k : Type) [Field k] [CharP k p] [PerfectRing k p]
    (ι : Zp2 p →+* WittVector p k) :
    (WittVector.frobenius : WittVector p k →+* WittVector p k).comp ι =
      ι.comp (WittVector.frobenius : Zp2 p →+* Zp2 p) := by
  rcases WittVector.eq_or_eq_comp_frobenius_of_ringHom_galoisField_two p k
      ((WittVector.frobenius : WittVector p k →+* WittVector p k).comp ι) ι with h | h
  · exact absurd h (frobenius_comp_ne k ι)
  · exact h

end Iota

end ShiftTransfer

namespace ShiftTransfer

open CerednikDrinfeld.FormalODModule CerednikDrinfeld.GradedCartierModuleData MvFormalGroup MvFormalGroup.CartierModule

open MvPowerSeries (subst HasSubst hasSubst_of_constantCoeff_zero constantCoeff)

section FrobCartier

variable {p : ℕ} [hp : Fact p.Prime] {C : Type} [CommRing C]

noncomputable abbrev frobSeries (C : Type) [CommRing C] (p : ℕ) : Series C :=
  fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) C) ^ p

theorem constantCoeff_frobSeries (i : Fin 2) : constantCoeff (frobSeries C p i) = 0 := by
  rw [map_pow, MvPowerSeries.constantCoeff_X, zero_pow hp.out.ne_zero]

omit hp in
theorem frobSeries_map {C' : Type} [CommRing C'] (g : C →+* C') :
    (frobSeries C p).map g = frobSeries C' p := by
  funext i
  show MvPowerSeries.map g ((MvPowerSeries.X i : MvPowerSeries (Fin 2) C) ^ p) = _
  rw [map_pow, MvPowerSeries.map_X]

theorem subst_X_pow_map_frobenius [CharP C p] {σ : Type*} (g : MvPowerSeries σ C) :
    subst (fun s : σ => (MvPowerSeries.X s : MvPowerSeries σ C) ^ p)
      (MvPowerSeries.map (frobenius C p) g) = g ^ p := by
  haveI : ExpChar C p := ExpChar.prime hp.out
  rw [show subst (fun s : σ => (MvPowerSeries.X s : MvPowerSeries σ C) ^ p)
      (MvPowerSeries.map (frobenius C p) g) = MvPowerSeries.expand p hp.out.ne_zero
        (MvPowerSeries.map (frobenius C p) g) by
      rw [MvPowerSeries.expand, MvPowerSeries.substAlgHom_apply],
    ← MvPowerSeries.map_expand, MvPowerSeries.map_frobenius_expand]

theorem toPowerSeries_verschiebungInt_charP [CharP C p] {d : ℕ} {F : MvFormalGroup d C} [F.IsComm]
    (f : CartierModule p F) (j : Fin d) :
    (verschiebungInt f).toPowerSeries j =
      subst (fun n : ℕ => (MvPowerSeries.X n : MvPowerSeries ℕ C) ^ p) (f.toPowerSeries j) := by
  rw [verschiebungInt_eq_verschiebung]
  rfl

theorem map_eq_of_comp_frobSeries [CharP C p] {F G K : MvFormalGroup 2 C} [F.IsComm] [G.IsComm] [K.IsComm]
    (H : F.Hom G) {A ρ' : Series C} (hA : IsLawHom G G A) (hρ' : IsLawHom K G ρ')
    (hH : H.toPowerSeries = A.comp (ρ'.comp (frobSeries C p)))
    (m : CartierModule p F) (m' : CartierModule p K)
    (hm' : ∀ l, m'.toPowerSeries l = MvPowerSeries.map (frobenius C p) (m.toPowerSeries l)) :
    CartierModule.map H m = CartierModule.map hA.toHom (CartierModule.map hρ'.toHom (verschiebungInt m')) := by
  apply CartierModule.ext
  funext i
  rw [toPowerSeries_map, toPowerSeries_map, hH]
  have hm0 := m.hasSubst_toPowerSeries
  have hρ0 : HasSubst ρ' := hρ'.hasSubst
  have hfr : HasSubst (frobSeries C p) := hasSubst_of_constantCoeff_zero constantCoeff_frobSeries
  have hρf : HasSubst (ρ'.comp (frobSeries C p)) :=
    hasSubst_of_constantCoeff_zero (Series.constantCoeff_comp hρ'.1 constantCoeff_frobSeries)

  have key : (fun j => subst m.toPowerSeries ((ρ'.comp (frobSeries C p)) j)) =
      (CartierModule.map hρ'.toHom (verschiebungInt m')).toPowerSeries := by
    funext j
    rw [toPowerSeries_map]
    show subst m.toPowerSeries (subst (frobSeries C p) (ρ' j)) =
      subst (verschiebungInt m').toPowerSeries (ρ' j)
    rw [MvPowerSeries.subst_comp_subst_apply hfr hm0]
    congr 1
    funext l
    show subst m.toPowerSeries ((MvPowerSeries.X l : MvPowerSeries (Fin 2) C) ^ p) =
      (verschiebungInt m').toPowerSeries l
    rw [MvPowerSeries.subst_pow hm0, MvPowerSeries.subst_X hm0, toPowerSeries_verschiebungInt_charP,
      hm', subst_X_pow_map_frobenius]
  show subst m.toPowerSeries (subst (ρ'.comp (frobSeries C p)) (A i)) = _
  rw [MvPowerSeries.subst_comp_subst_apply hρf hm0, key]
  rfl

theorem map_actEnd_natCast_pow (X : FormalODModule p C) (a : ℕ) (z : CartierModule p X.F) :
    CartierModule.map (X.actEnd ((p : Zp2 p) ^ a)) z = p ^ a • z := by
  have h : X.actEnd ((p : Zp2 p) ^ a) = ((p ^ a : ℕ) : MvFormalGroup.End X.F) := by
    rw [← actRingHom_apply, map_pow, map_natCast, Nat.cast_pow]
  rw [← endAct_apply, h, endAct_natCast]

end FrobCartier

section NMod

variable {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] {j : Zp2 p →+* B}
variable (D : GradedCartierModuleData p B j)

noncomputable def nu : D.NMod →+ D.NMod :=
  D.nMap D D.verschiebung (fun _ => rfl) (fun x => (D.varpi_verschiebung x).symm)

theorem nu_nMk (m m' : D.M) : nu D (D.nMk (m, m')) = D.nMk (D.verschiebung m, D.verschiebung m') := rfl

theorem nVarpi_nMk (m m' : D.M) : D.nVarpi (D.nMk (m, m')) = D.nMk (D.varpi m, D.varpi m') := rfl

theorem nsmul_nMk (n : ℕ) (m m' : D.M) : n • D.nMk (m, m') = D.nMk (n • m, n • m') := by
  rw [← map_nsmul]; rfl

theorem nMk_verschiebung_zero (u : D.M) : D.nMk (D.verschiebung u, 0) = D.nMk (0, D.varpi u) := by
  have h := D.nMk_verschiebung_neg_varpi u
  have : (D.verschiebung u, (0 : D.M)) = (D.verschiebung u, -D.varpi u) + (0, D.varpi u) := by
    ext <;> simp
  rw [this, map_add, h, zero_add]

theorem nu_eq_nMk_zero_lambda (m m' : D.M) :
    nu D (D.nMk (m, m')) = D.nMk (0, D.lambda (D.nMk (m, m'))) := by
  rw [nu_nMk, lambda_nMk]
  have : (D.verschiebung m, D.verschiebung m') = (D.verschiebung m, (0 : D.M)) + (0, D.verschiebung m') := by
    ext <;> simp
  rw [this, map_add, nMk_verschiebung_zero, ← map_add]
  congr 1
  ext <;> simp

theorem nVarpi_nVarpi (z : D.NMod) : D.nVarpi (D.nVarpi z) = p • z := by
  obtain ⟨⟨m, m'⟩, rfl⟩ := D.nMk_surjective z
  rw [nVarpi_nMk, nVarpi_nMk, D.varpi_varpi, D.varpi_varpi, nsmul_nMk]

theorem lambda_nMap {B' : Type} [CommRing B'] {j' : Zp2 p →+* B'} (D' : GradedCartierModuleData p B' j')
    (f : D.M →+ D'.M) (hV : ∀ x, f (D.verschiebung x) = D'.verschiebung (f x))
    (hPi : ∀ x, f (D.varpi x) = D'.varpi (f x)) (z : D.NMod) :
    D'.lambda (D.nMap D' f hV hPi z) = f (D.lambda z) := by
  obtain ⟨⟨m, m'⟩, rfl⟩ := D.nMk_surjective z
  rw [nMap_nMk, lambda_nMk, lambda_nMk, map_add, hPi, hV]

theorem nMap_nu {B' : Type} [CommRing B'] {j' : Zp2 p →+* B'} (D' : GradedCartierModuleData p B' j')
    (f : D.M →+ D'.M) (hV : ∀ x, f (D.verschiebung x) = D'.verschiebung (f x))
    (hPi : ∀ x, f (D.varpi x) = D'.varpi (f x)) (z : D.NMod) :
    D.nMap D' f hV hPi (nu D z) = nu D' (D.nMap D' f hV hPi z) := by
  obtain ⟨⟨m, m'⟩, rfl⟩ := D.nMk_surjective z
  rw [nu_nMk, nMap_nMk, nMap_nMk, nu_nMk, hV, hV]

theorem nMap_nVarpi {B' : Type} [CommRing B'] {j' : Zp2 p →+* B'} (D' : GradedCartierModuleData p B' j')
    (f : D.M →+ D'.M) (hV : ∀ x, f (D.verschiebung x) = D'.verschiebung (f x))
    (hPi : ∀ x, f (D.varpi x) = D'.varpi (f x)) (z : D.NMod) :
    D.nMap D' f hV hPi (D.nVarpi z) = D'.nVarpi (D.nMap D' f hV hPi z) := by
  obtain ⟨⟨m, m'⟩, rfl⟩ := D.nMk_surjective z
  rw [nVarpi_nMk, nMap_nMk, nMap_nMk, nVarpi_nMk, hPi, hPi]

theorem nMap_nsmul' {B' : Type} [CommRing B'] {j' : Zp2 p →+* B'} (D' : GradedCartierModuleData p B' j')
    (f : D.M →+ D'.M) (hV : ∀ x, f (D.verschiebung x) = D'.verschiebung (f x))
    (hPi : ∀ x, f (D.varpi x) = D'.varpi (f x)) (n : ℕ) (z : D.NMod) :
    D.nMap D' f hV hPi (n • z) = n • D.nMap D' f hV hPi z :=
  map_nsmul _ n z

theorem varpi_lambda_eq_of_mem_eta (hVF : ∀ x : D.M, D.verschiebung (D.frobenius x) = (p : ℕ) • x)
    (L : D.M →+ D.NMod) (hL : D.IsCartierLMap L) (z : D.NMod)
    (hz : z ∈ D.eta L hL.map_verschiebung) :
    D.varpi (D.lambda z) = D.verschiebung (D.lambda z) := by
  obtain ⟨⟨x, x'⟩, rfl⟩ := D.nMk_surjective z
  rw [mem_eta_iff, phi_nMk] at hz

  have hLx : L x = D.nMk (x - x', x') := by
    have : D.nMk (x - x', x') = D.nMk (x, x') - D.nMk (x', 0) := by
      rw [← map_sub]; congr 1; ext <;> simp
    rw [this, ← hz, add_sub_cancel_right]

  have hFx : D.frobenius x = D.varpi (x - x') + D.verschiebung x' := by
    rw [← hL.lambda_comp x, hLx, lambda_nMk]
  rw [lambda_nMk, map_add, map_add, D.varpi_varpi, D.varpi_verschiebung]

  have hpx : (p : ℕ) • x = D.verschiebung (D.varpi (x - x')) + D.verschiebung (D.verschiebung x') := by
    rw [← hVF, hFx, map_add]
  rw [hpx, map_sub, map_sub]
  abel

theorem nsmul_nu_eq_nsmul_nVarpi (hVF : ∀ x : D.M, D.verschiebung (D.frobenius x) = (p : ℕ) • x)
    (y : D.NMod) (hy : D.varpi (D.lambda y) = D.verschiebung (D.lambda y)) :
    (p : ℕ) • nu D y = (p : ℕ) • D.nVarpi y := by
  obtain ⟨⟨a, b⟩, rfl⟩ := D.nMk_surjective y
  rw [nu_eq_nMk_zero_lambda, nVarpi_nMk, nsmul_nMk, nsmul_nMk, smul_zero]
  set m := D.lambda (D.nMk (a, b)) with hm
  have hm' : m = D.varpi a + D.verschiebung b := by rw [hm, lambda_nMk]

  have h1 : D.nMk ((p : ℕ) • D.varpi a, (p : ℕ) • D.varpi b) =
      D.nMk (0, D.varpi (D.frobenius (D.varpi a)) + (p : ℕ) • D.varpi b) := by
    rw [← hVF (D.varpi a)]
    have : (D.verschiebung (D.frobenius (D.varpi a)), (p : ℕ) • D.varpi b) =
        (D.verschiebung (D.frobenius (D.varpi a)), (0 : D.M)) + (0, (p : ℕ) • D.varpi b) := by
      ext <;> simp
    rw [this, map_add, nMk_verschiebung_zero, ← map_add]
    congr 1; ext <;> simp
  rw [h1]
  congr 1
  ext
  · rfl
  · show (p : ℕ) • m = D.varpi (D.frobenius (D.varpi a)) + (p : ℕ) • D.varpi b

    rw [D.varpi_frobenius, D.varpi_varpi, map_nsmul]

    have he : (p : ℕ) • (m - D.frobenius a - D.varpi b) = 0 := by
      rw [← D.frobenius_verschiebung]
      suffices hV0 : D.verschiebung (m - D.frobenius a - D.varpi b) = 0 by rw [hV0, map_zero]
      rw [map_sub, map_sub, hVF a, ← hy, hm', map_add, D.varpi_varpi, D.varpi_verschiebung]
      abel
    rw [smul_sub, smul_sub, sub_sub, sub_eq_zero] at he
    rw [he]

theorem nsmul_eq_nsmul_of_nu (hVF : ∀ x : D.M, D.verschiebung (D.frobenius x) = (p : ℕ) • x)
    (r r' : D.NMod) (a b : ℕ)
    (h1 : p ^ a • nu D r' = p ^ b • D.nVarpi r)
    (h2 : D.varpi (D.lambda r') = D.verschiebung (D.lambda r')) :
    p ^ (a + 2) • r' = p ^ (b + 2) • r := by
  have h3 : (p : ℕ) • nu D r' = (p : ℕ) • D.nVarpi r' := nsmul_nu_eq_nsmul_nVarpi D hVF r' h2

  have h4 : p ^ (a + 1) • D.nVarpi r' = p ^ (b + 1) • D.nVarpi r := by
    calc p ^ (a + 1) • D.nVarpi r' = p ^ a • ((p : ℕ) • D.nVarpi r') := by rw [pow_succ, ← smul_smul]
      _ = p ^ a • ((p : ℕ) • nu D r') := by rw [h3]
      _ = (p : ℕ) • (p ^ a • nu D r') := by rw [smul_smul, smul_smul, mul_comm]
      _ = (p : ℕ) • (p ^ b • D.nVarpi r) := by rw [h1]
      _ = p ^ (b + 1) • D.nVarpi r := by rw [smul_smul, ← pow_succ']
  have h5 := congrArg D.nVarpi h4
  rw [map_nsmul, map_nsmul, nVarpi_nVarpi, nVarpi_nVarpi, smul_smul, smul_smul, ← pow_succ,
    ← pow_succ] at h5
  rw [show a + 2 = a + 1 + 1 from rfl, show b + 2 = b + 1 + 1 from rfl]
  exact h5

end NMod

end ShiftTransfer

namespace ShiftTransfer

open CerednikDrinfeld.FormalODModule CerednikDrinfeld.GradedCartierModuleData MvFormalGroup MvFormalGroup.CartierModule

open MvPowerSeries (subst HasSubst hasSubst_of_constantCoeff_zero constantCoeff)

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

theorem wittVector_mem_span_p_of_coeff_zero (k : Type) [Field k] [CharP k p] [PerfectRing k p]
    (z : WittVector p k) (hz : z.coeff 0 = 0) : z ∈ Ideal.span {(p : WittVector p k)} := by
  have hV : WittVector.verschiebung (z.shift 1) = z := by
    have h1 := WittVector.verschiebung_shift z 0 (by intro i hi; interval_cases i; exact hz)
    have h0 : z.shift 0 = z := by ext n; rw [WittVector.shift_coeff, zero_add]
    rw [h0] at h1
    exact h1
  obtain ⟨y, hy⟩ := (WittVector.frobenius_bijective p k).2 (z.shift 1)
  rw [Ideal.mem_span_singleton']
  refine ⟨y, ?_⟩
  rw [← hV, ← hy, WittVector.verschiebung_frobenius]

theorem residueMap_comp_frobenius_apply (k : Type) [Field k] [CharP k p] [PerfectRing k p]
    {B : Type} [CommRing B] (ψ : WittVector p k →+* B) (x : WittVector p k) :
    residueMap (p := p) (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k))
        (Ideal.Quotient.mk _ x) =
      (residueMap (p := p) ψ (Ideal.Quotient.mk _ x)) ^ p := by
  show Ideal.Quotient.mk (pIdeal p B) (ψ (WittVector.frobenius x)) =
    (Ideal.Quotient.mk (pIdeal p B) (ψ x)) ^ p
  rw [← map_pow, ← map_pow, Ideal.Quotient.eq, ← map_sub]
  have hmem : WittVector.frobenius x - x ^ p ∈ Ideal.span {(p : WittVector p k)} := by
    apply wittVector_mem_span_p_of_coeff_zero
    show WittVector.constantCoeff (WittVector.frobenius x - x ^ p) = 0
    rw [map_sub, map_pow]
    show (WittVector.frobenius x).coeff 0 - (x.coeff 0) ^ p = 0
    rw [WittVector.coeff_frobenius_charP, sub_self]
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hmem
  rw [← ha, map_mul, map_natCast]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)

end WittFacts

section Dictionary

variable {p : ℕ} [hp : Fact p.Prime] {S : Type} [CommRing S]
variable (Y : FormalODModule p S) (c' : Y.F.IsComm) (act' : Zp2 p → Series S)
  (l1 : ∀ a, IsLawHom Y.F Y.F (act' a)) (l2 : IsLawHom Y.F Y.F Y.varpi) (l3 : act' 1 = Series.id S)
  (l4 : ∀ a b, act' (a * b) = (act' a).comp (act' b))
  (l5 : ∀ a b, act' (a + b) = Series.addVia Y.F (act' a) (act' b))
  (l6 : Y.varpi.comp Y.varpi = act' (p : Zp2 p))
  (l7 : ∀ a, Y.varpi.comp (act' a) = (act' (WittVector.frobenius a)).comp Y.varpi)
  (hact : ∀ a, act' a = Y.act (WittVector.frobenius a))
  (j j' : Zp2 p →+* S) (hj : j' = j.comp (WittVector.frobenius : Zp2 p →+* Zp2 p))

def twist : FormalODModule p S := FormalODModule.mk Y.F c' act' Y.varpi l1 l2 l3 l4 l5 l6 l7

omit hact hj in
theorem twist_actEnd_toPowerSeries (a : Zp2 p) :
    ((twist Y c' act' l1 l2 l3 l4 l5 l6 l7).actEnd a).toPowerSeries = act' a := rfl

include hact in
theorem actEnd_twist (a : Zp2 p) :
    (twist Y c' act' l1 l2 l3 l4 l5 l6 l7).actEnd a = Y.actEnd (WittVector.frobenius a) :=
  MvFormalGroup.Hom.ext (by rw [twist_actEnd_toPowerSeries]; exact hact a)

include hact hj in
theorem gradedPiece_twist (n : ℕ) :
    (twist Y c' act' l1 l2 l3 l4 l5 l6 l7).gradedPiece j' n = Y.gradedPiece j n := by
  ext f
  simp only [FormalODModule.mem_gradedPiece_iff, actEnd_twist Y c' act' l1 l2 l3 l4 l5 l6 l7 hact, hj,
    RingHom.comp_apply, Zp2.frobenius_teichmuller]
  constructor <;> intro h c
  · have hc : (c ^ p) ^ p = c := by rw [← pow_mul, ← pow_two, FormalODModule.pow_card_galoisField]
    have := h (c ^ p)
    rwa [hc] at this
  · exact h (c ^ p)

include hact in
theorem lieAct_twist (a : Zp2 p) :
    (twist Y c' act' l1 l2 l3 l4 l5 l6 l7).lieAct a = Y.lieAct (WittVector.frobenius a) := by
  show Matrix.mulVecLin (MvFormalGroup.linearPart (act' a)) = Matrix.mulVecLin (MvFormalGroup.linearPart _)
  rw [hact]

include hact hj in
theorem lieZero_twist : (twist Y c' act' l1 l2 l3 l4 l5 l6 l7).lieZero j' = Y.lieZero j := by
  unfold FormalODModule.lieZero
  apply le_antisymm
  · refine le_iInf fun b => ?_
    obtain ⟨a, rfl⟩ := (Zp2.frobenius_bijective (p := p)).2 b
    refine (iInf_le _ a).trans (le_of_eq ?_)
    rw [lieAct_twist Y c' act' l1 l2 l3 l4 l5 l6 l7 hact, hj, RingHom.comp_apply]
  · refine le_iInf fun a => (iInf_le _ (WittVector.frobenius a)).trans (le_of_eq ?_)
    rw [lieAct_twist Y c' act' l1 l2 l3 l4 l5 l6 l7 hact, hj, RingHom.comp_apply]

include hact hj in
theorem lieOne_twist : (twist Y c' act' l1 l2 l3 l4 l5 l6 l7).lieOne j' = Y.lieOne j := by
  unfold FormalODModule.lieOne
  apply le_antisymm
  · refine le_iInf fun b => ?_
    obtain ⟨a, rfl⟩ := (Zp2.frobenius_bijective (p := p)).2 b
    refine (iInf_le _ a).trans (le_of_eq ?_)
    rw [lieAct_twist Y c' act' l1 l2 l3 l4 l5 l6 l7 hact, hj, RingHom.comp_apply]
  · refine le_iInf fun a => (iInf_le _ (WittVector.frobenius a)).trans (le_of_eq ?_)
    rw [lieAct_twist Y c' act' l1 l2 l3 l4 l5 l6 l7 hact, hj, RingHom.comp_apply]

variable (hc : IsCompl (Y.gradedPiece j 0) (Y.gradedPiece j 1))
  (hc' : IsCompl ((twist Y c' act' l1 l2 l3 l4 l5 l6 l7).gradedPiece j' 0)
    ((twist Y c' act' l1 l2 l3 l4 l5 l6 l7).gradedPiece j' 1))

include hact hj in
theorem piece_twist (i : Fin 2) :
    ((twist Y c' act' l1 l2 l3 l4 l5 l6 l7).toGradedCartierModuleData j' hc').piece i =
      (Y.toGradedCartierModuleData j hc).piece i := by
  ext m
  show m ∈ (twist Y c' act' l1 l2 l3 l4 l5 l6 l7).gradedPiece j' i ↔ m ∈ Y.gradedPiece j i
  rw [gradedPiece_twist Y c' act' l1 l2 l3 l4 l5 l6 l7 hact j j' hj]
  exact Iff.rfl

include hact hj in
theorem nPiece_twist (i : Fin 2) :
    ((twist Y c' act' l1 l2 l3 l4 l5 l6 l7).toGradedCartierModuleData j' hc').nPiece i =
      (Y.toGradedCartierModuleData j hc).nPiece i := by
  unfold GradedCartierModuleData.nPiece
  rw [piece_twist Y c' act' l1 l2 l3 l4 l5 l6 l7 hact j j' hj hc hc' i]
  rfl

include hact hj in
theorem etaPiece_twist
    (L : (Y.toGradedCartierModuleData j hc).M →+ (Y.toGradedCartierModuleData j hc).NMod)
    (hL : ∀ x, L ((Y.toGradedCartierModuleData j hc).verschiebung x) =
      (Y.toGradedCartierModuleData j hc).nMk ((Y.toGradedCartierModuleData j hc).varpi x, 0))
    (hL' : ∀ x, L (((twist Y c' act' l1 l2 l3 l4 l5 l6 l7).toGradedCartierModuleData j' hc').verschiebung x) =
      ((twist Y c' act' l1 l2 l3 l4 l5 l6 l7).toGradedCartierModuleData j' hc').nMk
        (((twist Y c' act' l1 l2 l3 l4 l5 l6 l7).toGradedCartierModuleData j' hc').varpi x, 0))
    (i : Fin 2) :
    ((twist Y c' act' l1 l2 l3 l4 l5 l6 l7).toGradedCartierModuleData j' hc').etaPiece L hL' i =
      (Y.toGradedCartierModuleData j hc).etaPiece L hL i := by
  unfold GradedCartierModuleData.etaPiece
  rw [nPiece_twist Y c' act' l1 l2 l3 l4 l5 l6 l7 hact j j' hj hc hc' i]
  rfl

omit hact hj in
theorem isCartierLMap_twist_iff
    (L : (Y.toGradedCartierModuleData j hc).M →+ (Y.toGradedCartierModuleData j hc).NMod) :
    ((twist Y c' act' l1 l2 l3 l4 l5 l6 l7).toGradedCartierModuleData j' hc').IsCartierLMap L ↔
      (Y.toGradedCartierModuleData j hc).IsCartierLMap L :=
  ⟨fun h => ⟨h.map_smul, h.map_verschiebung, h.lambda_comp⟩,
   fun h => ⟨h.map_smul, h.map_verschiebung, h.lambda_comp⟩⟩

include hact hj in
theorem isHomogeneousVBasis_twist_iff (γ : Fin 2 → CartierModule p Y.F) :
    ((twist Y c' act' l1 l2 l3 l4 l5 l6 l7).toGradedCartierModuleData j' hc').IsHomogeneousVBasis γ ↔
      (Y.toGradedCartierModuleData j hc).IsHomogeneousVBasis γ := by
  have hpiece := piece_twist Y c' act' l1 l2 l3 l4 l5 l6 l7 hact j j' hj hc hc'
  unfold GradedCartierModuleData.IsHomogeneousVBasis
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun i => (hpiece i) ▸ h1 i, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun i => (hpiece i).symm ▸ h1 i, h2⟩

include hact hj in
theorem isCanonicalLMap_twist_iff
    (L : (Y.toGradedCartierModuleData j hc).M →+ (Y.toGradedCartierModuleData j hc).NMod) :
    ((twist Y c' act' l1 l2 l3 l4 l5 l6 l7).toGradedCartierModuleData j' hc').IsCanonicalLMap L ↔
      (Y.toGradedCartierModuleData j hc).IsCanonicalLMap L := by
  have hpiece := piece_twist Y c' act' l1 l2 l3 l4 l5 l6 l7 hact j j' hj hc hc'
  constructor
  · intro h
    refine ⟨(isCartierLMap_twist_iff Y c' act' l1 l2 l3 l4 l5 l6 l7 j j' hc hc' L).mp h.isCartierLMap, ?_⟩
    obtain ⟨T, instT, jT, φ, hφ, htf, Dl, hDl, f, hf, Ll, hLl, hcomp⟩ := h.exists_lift
    refine ⟨T, instT, jT, φ, hφ, htf, Dl, hDl, f, ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, ?_, ?_⟩, Ll, hLl, hcomp⟩
    · intro i x hx
      rw [← hpiece i]; exact hf.2.2.2.2.1 i x hx
    · obtain ⟨γ, hγ, hγ'⟩ := hf.2.2.2.2.2
      exact ⟨γ, hγ, (isHomogeneousVBasis_twist_iff Y c' act' l1 l2 l3 l4 l5 l6 l7 hact j j' hj hc hc' _).mp hγ'⟩
  · intro h
    refine ⟨(isCartierLMap_twist_iff Y c' act' l1 l2 l3 l4 l5 l6 l7 j j' hc hc' L).mpr h.isCartierLMap, ?_⟩
    obtain ⟨T, instT, jT, φ, hφ, htf, Dl, hDl, f, hf, Ll, hLl, hcomp⟩ := h.exists_lift
    refine ⟨T, instT, jT, φ, hφ, htf, Dl, hDl, f, ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, ?_, ?_⟩, Ll, hLl, hcomp⟩
    · intro i x hx
      rw [hpiece i]; exact hf.2.2.2.2.1 i x hx
    · obtain ⟨γ, hγ, hγ'⟩ := hf.2.2.2.2.2
      exact ⟨γ, hγ, (isHomogeneousVBasis_twist_iff Y c' act' l1 l2 l3 l4 l5 l6 l7 hact j j' hj hc hc' _).mpr hγ'⟩

end Dictionary

section LatticeRelSlack

variable {p : ℕ} [hp : Fact p.Prime] {S : Type} [CommRing S]

theorem latticeRel_iff_of_nsmul_eq {jS : Zp2 p →+* S} (E : GradedCartierModuleData p S jS)
    {n n' A B : ℕ} (r r' : (Fin 2 → ℤ_[p]) →+ E.NMod) (hAB : A + n' = B + n)
    (h : ∀ w, p ^ A • r' w = p ^ B • r w) (zbar : E.NMod) (v : Fin 2 → ℚ_[p]) :
    Rigidified.LatticeRel E n' r' zbar v ↔ Rigidified.LatticeRel E n r zbar v := by
  constructor
  · rintro ⟨m, k, w, hv, hk⟩
    refine ⟨m, k + B, w, hv, ?_⟩
    have e1 : p ^ (k + B) • r w = p ^ k • (p ^ A • r' w) := by rw [h w, smul_smul, ← pow_add]
    rw [e1, smul_smul, mul_comm, ← smul_smul, hk, smul_smul, ← pow_add]
    rw [show A + (k + n' + m) = k + B + n + m by omega]
  · rintro ⟨m, k, w, hv, hk⟩
    refine ⟨m, k + A, w, hv, ?_⟩
    have e1 : p ^ (k + A) • r' w = p ^ k • (p ^ B • r w) := by rw [← h w, smul_smul, ← pow_add]
    rw [e1, smul_smul, mul_comm, ← smul_smul, hk, smul_smul, ← pow_add]
    rw [show B + (k + n + m) = k + A + n' + m by omega]

end LatticeRelSlack

end ShiftTransfer

namespace ShiftTransfer

open CerednikDrinfeld.FormalODModule CerednikDrinfeld.GradedCartierModuleData MvFormalGroup MvFormalGroup.CartierModule

open MvPowerSeries (subst HasSubst hasSubst_of_constantCoeff_zero constantCoeff)

section Main

variable {p : ℕ} [hp : Fact p.Prime]

theorem cartierModule_subsingleton {C : Type} [CommRing C] [Subsingleton C] {d : ℕ}
    (F : MvFormalGroup d C) : Subsingleton (CartierModule p F) := by
  constructor
  intro a b
  apply CartierModule.ext
  funext i
  ext e
  exact Subsingleton.elim _ _

theorem heartM (k : Type) [Field k] [CharP k p] [PerfectRing k p]
    {Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k))}
    {B : Type} [CommRing B] (ψ : WittVector p k →+* B)
    (t : Rigidified p Φ B) (n' : ℕ) (ρ' : Series (B ⧸ pIdeal p B)) (h0ρ' : ∀ i, constantCoeff (ρ' i) = 0)
    (hODt : IsODHom (t.Φbar ψ) t.Xbar t.ρ)
    (c : ℕ)
    (hc : (t.Xbar.act ((p : Zp2 p) ^ (c + t.n))).comp
        (ρ'.comp fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal p B)) ^ p) =
      (t.Xbar.act ((p : Zp2 p) ^ (c + n'))).comp (t.ρ.comp (Φ.varpi.map (residueMap ψ))))
    {S : Type} [CommRing S] (g : B →+* S)
    (hρ'S : IsLawHom (Rigidified.PhibarS (Φ := Φ) (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) g).F (t.XbarS g).F (ρ'.map (reduceMap g)))
    (m₀ : CartierModule p Φ.F) :
    p ^ (c + t.n) • verschiebungInt
        (CartierModule.map hρ'S.toHom (Rigidified.bcPhi (Φ := Φ) (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) g m₀)) =
      p ^ (c + n') • endAct (t.XbarS g).varpiEnd (Rigidified.rhoC ψ t hODt.1 g (Rigidified.bcPhi (Φ := Φ) ψ g m₀)) := by
  rcases subsingleton_or_nontrivial (S ⧸ pIdeal p S) with hS | hS
  · haveI := cartierModule_subsingleton (p := p) (t.XbarS g).F
    exact Subsingleton.elim _ _
  haveI : CharP (S ⧸ pIdeal p S) p := (CharP.charP_iff_prime_eq_zero hp.out).mpr (by
    rw [← map_natCast (Ideal.Quotient.mk (pIdeal p S)) p, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl)

  have hmid : IsLawHom (Rigidified.PhibarS (Φ := Φ) ψ g).F (t.XbarS g).F
      ((t.ρ.map (reduceMap g)).comp (Rigidified.PhibarS (Φ := Φ) ψ g).varpi) :=
    (hODt.1.map (reduceMap g)).comp (Rigidified.PhibarS (Φ := Φ) ψ g).isLawHom_varpi
  have hHlaw : IsLawHom (Rigidified.PhibarS (Φ := Φ) ψ g).F (t.XbarS g).F
      (((t.XbarS g).act ((p : Zp2 p) ^ (c + n'))).comp
        ((t.ρ.map (reduceMap g)).comp (Rigidified.PhibarS (Φ := Φ) ψ g).varpi)) :=
    (IsODHom.act_natCast_pow (t.XbarS g) (c + n')).1.comp hmid
  have hA : IsLawHom (t.XbarS g).F (t.XbarS g).F ((t.XbarS g).act ((p : Zp2 p) ^ (c + t.n))) :=
    (t.XbarS g).isLawHom_act _

  have hH : hHlaw.toHom.toPowerSeries =
      ((t.XbarS g).act ((p : Zp2 p) ^ (c + t.n))).comp ((ρ'.map (reduceMap g)).comp (frobSeries _ p)) := by
    have key := congrArg (Series.map (reduceMap g)) hc
    have h0f : ∀ i, constantCoeff ((fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal p B)) ^ p) i) = 0 :=
      constantCoeff_frobSeries
    have h0Pi : ∀ i, constantCoeff ((Φ.varpi.map (residueMap ψ)) i) = 0 :=
      (Φ.map (residueMap ψ)).isLawHom_varpi.1
    rw [Series.map_comp _ _ _ (Series.constantCoeff_comp h0ρ' h0f), Series.map_comp _ _ _ h0f,
      Series.map_comp _ _ _ (Series.constantCoeff_comp hODt.constantCoeff h0Pi),
      Series.map_comp _ _ _ h0Pi] at key
    rw [IsLawHom.toHom_toPowerSeries, ← frobSeries_map (reduceMap g)]
    exact key.symm

  have hm' : ∀ l, (Rigidified.bcPhi (Φ := Φ) (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) g m₀).toPowerSeries l =
      MvPowerSeries.map (frobenius (S ⧸ pIdeal p S) p) ((Rigidified.bcPhi (Φ := Φ) ψ g m₀).toPowerSeries l) := by
    intro l
    show MvPowerSeries.map (reduceMap g) (MvPowerSeries.map (residueMap (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k))) (m₀.toPowerSeries l)) =
      MvPowerSeries.map (frobenius (S ⧸ pIdeal p S) p)
        (MvPowerSeries.map (reduceMap g) (MvPowerSeries.map (residueMap ψ) (m₀.toPowerSeries l)))
    ext e
    simp only [MvPowerSeries.coeff_map]
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (MvPowerSeries.coeff e (m₀.toPowerSeries l))
    rw [← hx, residueMap_comp_frobenius_apply k ψ x, map_pow, frobenius_def]
  have E0 := map_eq_of_comp_frobSeries hHlaw.toHom hA hρ'S hH (Rigidified.bcPhi (Φ := Φ) ψ g m₀)
    (Rigidified.bcPhi (Φ := Φ) (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) g m₀) hm'

  have e3 : CartierModule.map hmid.toHom (Rigidified.bcPhi (Φ := Φ) ψ g m₀) =
      Rigidified.rhoC ψ t hODt.1 g (endAct (Rigidified.PhibarS (Φ := Φ) ψ g).varpiEnd
        (Rigidified.bcPhi (Φ := Φ) ψ g m₀)) := by
    rw [endAct_apply]
    exact map_comp ((hODt.1.map (reduceMap g)).toHom) (Rigidified.PhibarS (Φ := Φ) ψ g).varpiEnd _
  have eL : CartierModule.map hHlaw.toHom (Rigidified.bcPhi (Φ := Φ) ψ g m₀) =
      p ^ (c + n') • endAct (t.XbarS g).varpiEnd (Rigidified.rhoC ψ t hODt.1 g (Rigidified.bcPhi (Φ := Φ) ψ g m₀)) := by
    rw [show hHlaw.toHom = ((t.XbarS g).actEnd ((p : Zp2 p) ^ (c + n'))).comp hmid.toHom from
        MvFormalGroup.Hom.ext rfl, map_comp, map_actEnd_natCast_pow, e3,
      Rigidified.rhoC_endAct_varpiEnd ψ t hODt g]

  have eR : CartierModule.map hA.toHom (CartierModule.map hρ'S.toHom
      (verschiebungInt (Rigidified.bcPhi (Φ := Φ) (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) g m₀))) =
      p ^ (c + t.n) • verschiebungInt (CartierModule.map hρ'S.toHom (Rigidified.bcPhi (Φ := Φ) (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) g m₀)) := by
    rw [show hA.toHom = (t.XbarS g).actEnd ((p : Zp2 p) ^ (c + t.n)) from MvFormalGroup.Hom.ext rfl,
      map_actEnd_natCast_pow, map_verschiebungInt]
  rw [eL, eR] at E0
  exact E0.symm

theorem main
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι))
    (hΦ4 : Φ.HasHeight 4)
    (hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0)
      (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
    (hrΦ : ∀ (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+
        (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
      (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L),
      Set.BijOn rΦ Set.univ
        ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L
          hL.isCartierLMap.map_verschiebung 0 : Set _))
    {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : WittVector p k →+* B)
    (hB : IsNilpotent (p : B))
    (t t' : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ)
    (ht' : t'.IsAdmissible ι (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)))
    (hπ : Rigidified.IsPiTranslate ψ t t')
    (Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B)
    (hQ : t.IsCartierQuadruple ι hcΦ rΦ ψ Q) :
    t'.IsCartierQuadruple ι hcΦ rΦ (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) Q := by

  obtain ⟨X', n', ρ'⟩ := t'
  obtain ⟨F', hcomm', act', varpi', l1, l2, l3, l4, l5, l6, l7⟩ := X'
  obtain ⟨hF, hϖ, hact, c, hc⟩ := hπ
  change F' = t.X.F at hF
  change varpi' = t.X.varpi at hϖ
  subst hF
  subst hϖ
  replace hact : ∀ a, act' a = t.X.act (WittVector.frobenius a) := hact
  haveI : ExpChar k p := ExpChar.prime (Fact.out : p.Prime)
  haveI : PerfectRing k p := inferInstance

  have hj : structureMap ι (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) = (structureMap ι ψ).comp (WittVector.frobenius : Zp2 p →+* Zp2 p) := by
    show (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)).comp ι = (ψ.comp ι).comp _
    rw [RingHom.comp_assoc, frobenius_comp_eq_comp_frobenius k ι, ← RingHom.comp_assoc]
  have hjS : ∀ {S : Type} [CommRing S] (g : B →+* S),
      Rigidified.jS ι (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) g = (Rigidified.jS ι ψ g).comp (WittVector.frobenius : Zp2 p →+* Zp2 p) := by
    intro S _ g
    show g.comp (structureMap ι (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k))) = (g.comp (structureMap ι ψ)).comp _
    rw [hj]
    simp only [RingHom.comp_assoc]

  obtain ⟨hODt, τ₀, τ₁, hT0, hT1, H⟩ := hQ
  obtain ⟨LΦ, hLΦ⟩ :=
    CerednikDrinfeld.FormalODModule.exists_isCanonicalLMap_toGradedCartierModuleData_of_isSpecial_of_isAlgClosed
      p k ι Φ hΦ hcΦ
  have hp0Φ : ((p : ℕ) : WittVector p k ⧸ pIdeal p (WittVector p k)) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk (pIdeal p (WittVector p k))) p, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl
  have hVFΦ := verschiebung_frobenius_eq_nsmul
    (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ) hp0Φ
  have hyη : ∀ w, rΦ w ∈ (Φ.toGradedCartierModuleData _ hcΦ).eta LΦ hLΦ.isCartierLMap.map_verschiebung :=
    fun w => (AddSubgroup.mem_inf.mp ((hrΦ LΦ hLΦ).mapsTo (Set.mem_univ w))).1
  have hinvΦ : ∀ w, (Φ.toGradedCartierModuleData _ hcΦ).varpi ((Φ.toGradedCartierModuleData _ hcΦ).lambda (rΦ w)) =
      (Φ.toGradedCartierModuleData _ hcΦ).verschiebung ((Φ.toGradedCartierModuleData _ hcΦ).lambda (rΦ w)) :=
    fun w => varpi_lambda_eq_of_mem_eta _ hVFΦ LΦ hLΦ.isCartierLMap (rΦ w) (hyη w)

  set X' : FormalODModule p B :=
    (FormalODModule.mk t.X.F hcomm' act' t.X.varpi l1 l2 l3 l4 l5 l6 l7 : FormalODModule p B) with hX'
  have hOD' : IsODHom (Rigidified.Φbar (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) (⟨X', n', ρ'⟩ : Rigidified p Φ B))
      (⟨X', n', ρ'⟩ : Rigidified p Φ B).Xbar ρ' := ht'.2.2.1
  have h0ρ' : ∀ i, constantCoeff (ρ' i) = 0 := hOD'.constantCoeff

  have hactS : ∀ {S : Type} [CommRing S] (g : B →+* S) (a : Zp2 p),
      (X'.map g).act a = (t.XS g).act (WittVector.frobenius a) := by
    intro S _ g a
    show (act' a).map g = (t.X.act _).map g
    rw [hact]

  have heart : ∀ {S : Type} [CommRing S] (g : B →+* S)
      (hcb : t.IsGradedSbar ι ψ g) (hcΦg : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ g)
      (hcb' : (⟨X', n', ρ'⟩ : Rigidified p Φ B).IsGradedSbar ι (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) g)
      (hcΦg' : Rigidified.IsGradedPhiS (Φ := Φ) ι (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) g)
      (hODa : IsODHom (t.Φbar ψ) t.Xbar t.ρ)
      (hODb : IsODHom (Rigidified.Φbar (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) (⟨X', n', ρ'⟩ : Rigidified p Φ B))
        (⟨X', n', ρ'⟩ : Rigidified p Φ B).Xbar ρ')
      (w : Fin 2 → ℤ_[p]),
      p ^ (c + t.n + 2) • ((⟨X', n', ρ'⟩ : Rigidified p Φ B).rigidNum ι hcΦ rΦ (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) hODb g hcb' hcΦg' w :
          ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).NMod) =
        p ^ (c + n' + 2) • t.rigidNum ι hcΦ rΦ ψ hODa g hcb hcΦg w := by
    intro S _ g hcb hcΦg hcb' hcΦg' hODa hODb w
    set Dbar := (t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb with hDbar
    have hρ'S : IsLawHom (Rigidified.PhibarS (Φ := Φ) (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) g).F (t.XbarS g).F (ρ'.map (reduceMap g)) :=
      hODb.1.map (reduceMap g)
    have hrho : ∀ m, Rigidified.rhoC (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) (⟨X', n', ρ'⟩ : Rigidified p Φ B) hODb.1 g m =
        CartierModule.map hρ'S.toHom m := fun m => rfl
    have hp0S : ((p : ℕ) : S ⧸ pIdeal p S) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk (pIdeal p S)) p, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span rfl
    have hVF := verschiebung_frobenius_eq_nsmul Dbar hp0S
    apply nsmul_eq_nsmul_of_nu Dbar hVF
    ·
      obtain ⟨⟨m₁, m₂⟩, hy⟩ := (Φ.toGradedCartierModuleData _ hcΦ).nMk_surjective (rΦ w)
      have e' : ((⟨X', n', ρ'⟩ : Rigidified p Φ B).rigidNum ι hcΦ rΦ (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) hODb g hcb' hcΦg' w : Dbar.NMod) =
          Dbar.nMk (CartierModule.map hρ'S.toHom (Rigidified.bcPhi (Φ := Φ) (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) g m₁),
            CartierModule.map hρ'S.toHom (Rigidified.bcPhi (Φ := Φ) (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) g m₂)) := by
        simp only [Rigidified.rigidNum, AddMonoidHom.coe_comp, Function.comp_apply, ← hy, nMap_nMk]
        rfl
      have e : t.rigidNum ι hcΦ rΦ ψ hODa g hcb hcΦg w =
          Dbar.nMk (Rigidified.rhoC ψ t hODa.1 g (Rigidified.bcPhi (Φ := Φ) ψ g m₁),
            Rigidified.rhoC ψ t hODa.1 g (Rigidified.bcPhi (Φ := Φ) ψ g m₂)) := by
        simp only [Rigidified.rigidNum, AddMonoidHom.coe_comp, Function.comp_apply, ← hy, nMap_nMk]
        rfl
      rw [e', e, nu_nMk, nVarpi_nMk, nsmul_nMk, nsmul_nMk]
      have h₁ := heartM k ψ t n' ρ' h0ρ' hODa c hc g hρ'S m₁
      have h₂ := heartM k ψ t n' ρ' h0ρ' hODa c hc g hρ'S m₂
      exact congrArg Dbar.nMk (Prod.ext h₁ h₂)
    ·
      have A2 := lambda_nMap (Φ.toGradedCartierModuleData _ hcΦ)
        ((Rigidified.PhibarS (Φ := Φ) (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) g).toGradedCartierModuleData (Rigidified.jPhiS ι (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) g) hcΦg')
        (Rigidified.bcPhi (Φ := Φ) (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) g) (Rigidified.bcPhi_verschiebungInt (Φ := Φ) (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) g)
        (Rigidified.bcPhi_endAct_varpiEnd (Φ := Φ) (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) g) (rΦ w)
      have A1 := lambda_nMap
        ((Rigidified.PhibarS (Φ := Φ) (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) g).toGradedCartierModuleData (Rigidified.jPhiS ι (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) g) hcΦg')
        (((⟨X', n', ρ'⟩ : Rigidified p Φ B).XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) g) hcb')
        (Rigidified.rhoC (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) (⟨X', n', ρ'⟩ : Rigidified p Φ B) hODb.1 g)
        (Rigidified.rhoC_verschiebungInt (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) (⟨X', n', ρ'⟩ : Rigidified p Φ B) hODb.1 g)
        (Rigidified.rhoC_endAct_varpiEnd (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) (⟨X', n', ρ'⟩ : Rigidified p Φ B) hODb g)
        ((Φ.toGradedCartierModuleData _ hcΦ).nMap
          ((Rigidified.PhibarS (Φ := Φ) (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) g).toGradedCartierModuleData (Rigidified.jPhiS ι (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) g) hcΦg')
          (Rigidified.bcPhi (Φ := Φ) (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) g)
          (Rigidified.bcPhi_verschiebungInt (Φ := Φ) (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) g) (Rigidified.bcPhi_endAct_varpiEnd (Φ := Φ) (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) g) (rΦ w))
      rw [A2] at A1
      have eLam : Dbar.lambda ((⟨X', n', ρ'⟩ : Rigidified p Φ B).rigidNum ι hcΦ rΦ (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) hODb g hcb' hcΦg' w) =
          CartierModule.map hρ'S.toHom (Rigidified.bcPhi (Φ := Φ) (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) g
            ((Φ.toGradedCartierModuleData _ hcΦ).lambda (rΦ w))) := A1
      have hPi' : ∀ m : CartierModule p (Rigidified.PhibarS (Φ := Φ) (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) g).F,
          endAct (t.XbarS g).varpiEnd (CartierModule.map hρ'S.toHom m) =
          CartierModule.map hρ'S.toHom (endAct (Rigidified.PhibarS (Φ := Φ) (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) g).varpiEnd m) := by
        intro m
        have hce : (t.XbarS g).varpiEnd.comp hρ'S.toHom =
            hρ'S.toHom.comp (Rigidified.PhibarS (Φ := Φ) (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) g).varpiEnd :=
          MvFormalGroup.Hom.ext ((hODb.map (reduceMap g)).2.2).symm
        have hcm := congrArg (fun φ => CartierModule.map φ m) hce
        simp only [map_comp] at hcm
        exact hcm
      rw [eLam]
      show endAct (t.XbarS g).varpiEnd _ = verschiebungInt _
      rw [hPi', ← Rigidified.bcPhi_endAct_varpiEnd (Φ := Φ) (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) g]
      rw [show endAct Φ.varpiEnd ((Φ.toGradedCartierModuleData _ hcΦ).lambda (rΦ w)) =
          verschiebungInt ((Φ.toGradedCartierModuleData _ hcΦ).lambda (rΦ w)) from hinvΦ w]
      rw [Rigidified.bcPhi_verschiebungInt, map_verschiebungInt]

  have hnilS : ∀ f : B, IsNilpotent ((p : ℕ) : Rigidified.Baway f) := fun f => by
    have := hB.map (Rigidified.awayHom f)
    rwa [map_natCast] at this
  have hnilSbar : ∀ {S : Type} [CommRing S], IsNilpotent ((p : ℕ) : S ⧸ pIdeal p S) := by
    intro S _
    refine ⟨1, ?_⟩
    rw [pow_one, ← map_natCast (Ideal.Quotient.mk (pIdeal p S)) p, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl
  have grS : ∀ (f : B), t.IsGradedS ι ψ (Rigidified.awayHom f) := fun f =>
    CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent p _ (hnilS f) _
  have grS' : ∀ (f : B), (⟨X', n', ρ'⟩ : Rigidified p Φ B).IsGradedS ι (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) (Rigidified.awayHom f) := fun f =>
    CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent p _ (hnilS f) _
  have grSbar : ∀ (f : B), t.IsGradedSbar ι ψ (Rigidified.awayHom f) := fun f =>
    CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent p _ hnilSbar _
  have grSbar' : ∀ (f : B), (⟨X', n', ρ'⟩ : Rigidified p Φ B).IsGradedSbar ι (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) (Rigidified.awayHom f) := fun f =>
    CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent p _ hnilSbar _
  have grΦ : ∀ (f : B), Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f) := fun f =>
    CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent p _ hnilSbar _
  have grΦ' : ∀ (f : B), Rigidified.IsGradedPhiS (Φ := Φ) ι (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) (Rigidified.awayHom f) := fun f =>
    CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent p _ hnilSbar _

  have canon : ∀ (f : B) (hc : t.IsGradedS ι ψ (Rigidified.awayHom f))
      (hc' : (⟨X', n', ρ'⟩ : Rigidified p Φ B).IsGradedS ι (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) (Rigidified.awayHom f))
      (L : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).M →+
        ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).NMod),
      (((⟨X', n', ρ'⟩ : Rigidified p Φ B).XS (Rigidified.awayHom f)).toGradedCartierModuleData
          (Rigidified.jS ι (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) (Rigidified.awayHom f)) hc').IsCanonicalLMap L ↔
        ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData
          (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).IsCanonicalLMap L := by
    intro f hc hc' L
    exact isCanonicalLMap_twist_iff (t.XS (Rigidified.awayHom f)) (X'.map (Rigidified.awayHom f)).isComm
      (X'.map (Rigidified.awayHom f)).act (X'.map (Rigidified.awayHom f)).isLawHom_act
      (t.XS (Rigidified.awayHom f)).isLawHom_varpi (X'.map (Rigidified.awayHom f)).act_one
      (X'.map (Rigidified.awayHom f)).act_mul (X'.map (Rigidified.awayHom f)).act_add
      (X'.map (Rigidified.awayHom f)).varpi_comp_varpi (X'.map (Rigidified.awayHom f)).varpi_comp_act
      (hactS _) _ _ (hjS _) hc hc' L
  have etaEq : ∀ (f : B) (hc : t.IsGradedS ι ψ (Rigidified.awayHom f))
      (hc' : (⟨X', n', ρ'⟩ : Rigidified p Φ B).IsGradedS ι (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) (Rigidified.awayHom f))
      (L : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).M →+
        ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).NMod)
      (hL : ∀ x, L (((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData
          (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).verschiebung x) =
        ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).nMk
          (((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).varpi x, 0))
      (hL' : ∀ x, L ((((⟨X', n', ρ'⟩ : Rigidified p Φ B).XS (Rigidified.awayHom f)).toGradedCartierModuleData
          (Rigidified.jS ι (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) (Rigidified.awayHom f)) hc').verschiebung x) =
        (((⟨X', n', ρ'⟩ : Rigidified p Φ B).XS (Rigidified.awayHom f)).toGradedCartierModuleData
          (Rigidified.jS ι (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) (Rigidified.awayHom f)) hc').nMk
          ((((⟨X', n', ρ'⟩ : Rigidified p Φ B).XS (Rigidified.awayHom f)).toGradedCartierModuleData
            (Rigidified.jS ι (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) (Rigidified.awayHom f)) hc').varpi x, 0))
      (i : Fin 2),
      (((⟨X', n', ρ'⟩ : Rigidified p Φ B).XS (Rigidified.awayHom f)).toGradedCartierModuleData
          (Rigidified.jS ι (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) (Rigidified.awayHom f)) hc').etaPiece L hL' i =
        ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData
          (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).etaPiece L hL i := by
    intro f hc hc' L hL hL' i
    exact etaPiece_twist (t.XS (Rigidified.awayHom f)) (X'.map (Rigidified.awayHom f)).isComm
      (X'.map (Rigidified.awayHom f)).act (X'.map (Rigidified.awayHom f)).isLawHom_act
      (t.XS (Rigidified.awayHom f)).isLawHom_varpi (X'.map (Rigidified.awayHom f)).act_one
      (X'.map (Rigidified.awayHom f)).act_mul (X'.map (Rigidified.awayHom f)).act_add
      (X'.map (Rigidified.awayHom f)).varpi_comp_varpi (X'.map (Rigidified.awayHom f)).varpi_comp_act
      (hactS _) _ _ (hjS _) hc hc' L hL hL' i
  have transfer : ∀ (f : B) (hODa : IsODHom (t.Φbar ψ) t.Xbar t.ρ)
      (hODb : IsODHom (Rigidified.Φbar (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) (⟨X', n', ρ'⟩ : Rigidified p Φ B))
        (⟨X', n', ρ'⟩ : Rigidified p Φ B).Xbar ρ')
      (hc : t.IsGradedS ι ψ (Rigidified.awayHom f)) (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f))
      (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
      (hc' : (⟨X', n', ρ'⟩ : Rigidified p Φ B).IsGradedS ι (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) (Rigidified.awayHom f))
      (hcb' : (⟨X', n', ρ'⟩ : Rigidified p Φ B).IsGradedSbar ι (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) (Rigidified.awayHom f))
      (hcΦf' : Rigidified.IsGradedPhiS (Φ := Φ) ι (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) (Rigidified.awayHom f))
      (L : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).M →+
        ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).NMod)
      (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData
          (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).IsCanonicalLMap L)
      (hL' : (((⟨X', n', ρ'⟩ : Rigidified p Φ B).XS (Rigidified.awayHom f)).toGradedCartierModuleData
          (Rigidified.jS ι (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) (Rigidified.awayHom f)) hc').IsCanonicalLMap L)
      (i : Fin 2) (z : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData
          (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).NMod) (v : Fin 2 → ℚ_[p]),
      t.IsEtaSection ι hcΦ rΦ ψ hODa (Rigidified.awayHom f) hc hcb hcΦf L hL i z v ↔
        (⟨X', n', ρ'⟩ : Rigidified p Φ B).IsEtaSection ι hcΦ rΦ (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) hODb (Rigidified.awayHom f)
          hc' hcb' hcΦf' L hL' i z v := by
    intro f hODa hODb hc hcb hcΦf hc' hcb' hcΦf' L hL hL' i z v
    unfold Rigidified.IsEtaSection
    refine and_congr ?_ ?_
    · rw [etaEq f hc hc' L hL.isCartierLMap.map_verschiebung hL'.isCartierLMap.map_verschiebung i]
      exact Iff.rfl
    · exact (latticeRel_iff_of_nsmul_eq
        ((t.XbarS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jSbar ι ψ _) hcb)
        (n := t.n) (n' := n') (A := c + t.n + 2) (B := c + n' + 2)
        (t.rigidNum ι hcΦ rΦ ψ hODa _ hcb hcΦf)
        ((⟨X', n', ρ'⟩ : Rigidified p Φ B).rigidNum ι hcΦ rΦ (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) hODb _ hcb' hcΦf') (by omega)
        (fun w => heart _ hcb hcΦf hcb' hcΦf' hODa hODb w) _ _).symm

  have hlie0 : X'.lieZero (structureMap ι (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k))) = t.X.lieZero (structureMap ι ψ) :=
    lieZero_twist t.X hcomm' act' l1 l2 l3 l4 l5 l6 l7 hact _ _ hj
  have hlie1 : X'.lieOne (structureMap ι (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k))) = t.X.lieOne (structureMap ι ψ) :=
    lieOne_twist t.X hcomm' act' l1 l2 l3 l4 l5 l6 l7 hact _ _ hj
  refine ⟨hOD', τ₀.trans (LinearEquiv.ofEq _ _ hlie0.symm), τ₁.trans (LinearEquiv.ofEq _ _ hlie1.symm),
    ?_, ?_, fun hODb x => ?_⟩
  · intro s
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply,
      LinearEquiv.coe_ofEq_apply]
    exact hT0 s
  · intro s
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply,
      LinearEquiv.coe_ofEq_apply]
    exact hT1 s
  obtain ⟨N0, N1, U0, U1⟩ := H hODt x
  refine ⟨fun v => ?_, fun v => ?_, ?_, ?_⟩
  · rw [N0 v]
    constructor
    · rintro ⟨f, hf, hc, hcb, hcΦf, L, hL, z, hz⟩
      exact ⟨f, hf, grS' f, grSbar' f, grΦ' f, L, (canon f hc (grS' f) L).mpr hL, z,
        (transfer f hODt hODb hc hcb hcΦf (grS' f) (grSbar' f) (grΦ' f) L hL _ 0 z v).mp hz⟩
    · rintro ⟨f, hf, hc', hcb', hcΦf', L, hL', z, hz⟩
      exact ⟨f, hf, grS f, grSbar f, grΦ f, L, (canon f (grS f) hc' L).mp hL', z,
        (transfer f hODt hODb (grS f) (grSbar f) (grΦ f) hc' hcb' hcΦf' L _ hL' 0 z v).mpr hz⟩
  · rw [N1 v]
    constructor
    · rintro ⟨f, hf, hc, hcb, hcΦf, L, hL, z, hz⟩
      exact ⟨f, hf, grS' f, grSbar' f, grΦ' f, L, (canon f hc (grS' f) L).mpr hL, z,
        (transfer f hODt hODb hc hcb hcΦf (grS' f) (grSbar' f) (grΦ' f) L hL _ 1 z v).mp hz⟩
    · rintro ⟨f, hf, hc', hcb', hcΦf', L, hL', z, hz⟩
      exact ⟨f, hf, grS f, grSbar f, grΦ f, L, (canon f (grS f) hc' L).mp hL', z,
        (transfer f hODt hODb (grS f) (grSbar f) (grΦ f) hc' hcb' hcΦf' L _ hL' 1 z v).mpr hz⟩
  · intro v hv f hf hc' hcb' hcΦf' L hL' z hz
    have hL := (canon f (grS f) hc' L).mp hL'
    have hz0 := (transfer f hODt hODb (grS f) (grSbar f) (grΦ f) hc' hcb' hcΦf' L hL hL' 0 z v).mpr hz
    obtain ⟨m, s, b, hm, hus, htan⟩ := U0 v hv f hf (grS f) (grSbar f) (grΦ f) L hL z hz0
    refine ⟨m, s, b, hm, hus, fun i => ?_⟩
    rw [LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply]
    exact htan i
  · intro v hv f hf hc' hcb' hcΦf' L hL' z hz
    have hL := (canon f (grS f) hc' L).mp hL'
    have hz1 := (transfer f hODt hODb (grS f) (grSbar f) (grΦ f) hc' hcb' hcΦf' L hL hL' 1 z v).mpr hz
    obtain ⟨m, s, b, hm, hus, htan⟩ := U1 v hv f hf (grS f) (grSbar f) (grΦ f) L hL z hz1
    refine ⟨m, s, b, hm, hus, fun i => ?_⟩
    rw [LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply]
    exact htan i

end Main

end ShiftTransfer

open ShiftTransfer in
theorem solution
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι))
    (hΦ4 : Φ.HasHeight 4)
    (hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0)
      (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
    (hrΦ : ∀ (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+
        (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
      (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L),
      Set.BijOn rΦ Set.univ
        ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L
          hL.isCartierLMap.map_verschiebung 0 : Set _))
    {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : WittVector p k →+* B)
    (hB : IsNilpotent (p : B))
    (t t' : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ)
    (ht' : t'.IsAdmissible ι (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)))
    (hπ : Rigidified.IsPiTranslate ψ t t')
    (Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B)
    (hQ : t.IsCartierQuadruple ι hcΦ rΦ ψ Q) :
    t'.IsCartierQuadruple ι hcΦ rΦ (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) Q :=
  ShiftTransfer.main p k ι Φ hΦ hΦ4 hcΦ rΦ hrΦ ψ hB t t' ht ht' hπ Q hQ

end S_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_comp_frobenius_of_isPiTranslate
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_comp_frobenius_of_isPiTranslate (solution)
