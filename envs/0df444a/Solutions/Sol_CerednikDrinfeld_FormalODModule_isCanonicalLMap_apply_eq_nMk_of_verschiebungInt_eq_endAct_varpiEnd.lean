-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.isCanonicalLMap_apply_eq_nMk_of_verschiebungInt_eq_endAct_varpiEnd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/6b7e6c17-d5c7-53bd-afb8-978aae326816

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
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_IsCartierLMap_exists_smul_apply_eq_nMk_of_torsionFree
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_isCanonicalLMap_apply_eq_nMk_of_verschiebungInt_eq_endAct_varpiEnd

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

noncomputable section

namespace LExplicit

open MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld.GradedCartierModuleData

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

end Datum

section Witt

variable {p : ℕ} [Fact p.Prime]

private theorem _root_.LExplicit.verschiebung_injective {R : Type} [CommRing R] :
    Function.Injective (WittVector.verschiebung : WittVector p R → WittVector p R) := by
  intro a b h
  ext n
  have := congrArg (fun w => w.coeff (n + 1)) h
  simpa only [WittVector.verschiebung_coeff_succ] using this

p2m_export "LExplicit" "verschiebung_injective"

theorem natCast_eq_verschiebung_one {R : Type} [CommRing R] [CharP R p] :
    ((p : ℕ) : WittVector p R) = WittVector.verschiebung 1 := by
  ext n
  rw [WittVector.coeff_p]
  cases n with
  | zero => rw [WittVector.verschiebung_coeff_zero, if_neg (Nat.zero_ne_one)]
  | succ n =>
    rw [WittVector.verschiebung_coeff_succ]
    cases n with
    | zero => simp
    | succ n => simp

theorem map_frobenius' {R S : Type} [CommRing R] [CommRing S] (g : R →+* S) (w : WittVector p R) :
    WittVector.map g (WittVector.frobenius w) = WittVector.frobenius (WittVector.map g w) :=
  (WittVector.frobenius_isPoly p).map g w

end Witt

end LExplicit

end

open LExplicit MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld.GradedCartierModuleData in
open CerednikDrinfeld CerednikDrinfeld.SpecialFormal in

theorem solution
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι)) (hΦ4 : Φ.HasHeight 4)
    (hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0) (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
    (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod) (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L)
    (i : ℕ) (hi : ∀ m ∈ Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) i,
      ∃ g : MvFormalGroup.CartierModule p Φ.F, MvFormalGroup.CartierModule.verschiebungInt g = MvFormalGroup.CartierModule.endAct Φ.varpiEnd m)
    (x y : MvFormalGroup.CartierModule p Φ.F) (hx : x ∈ Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) i)
    (hy : MvFormalGroup.CartierModule.verschiebungInt y = MvFormalGroup.CartierModule.endAct Φ.varpiEnd x) :
    L x = (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk (y, 0) := by
  classical

  have hmax : (pIdeal p (WittVector p k)).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (WittVector.irreducible p)
  haveI hchar : CharP (WittVector p k ⧸ pIdeal p (WittVector p k)) p :=
    CharP.quotient (WittVector p k) p (mem_nonunits_iff.2 (WittVector.irreducible p).not_isUnit)

  obtain ⟨S, instS, jS, φ, hφs, hS, Dl, hDl, f, hf, Ll, hLl, hpush⟩ := hL.exists_lift
  obtain ⟨hsemi, hF, hfV, hfPi, hpieces, γl, hγl, hγ⟩ := hf

  set i' : Fin 2 := ⟨i % 2, Nat.mod_lt i (by norm_num)⟩ with hi'def
  have hpiece_eq : Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) i = Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) (i' : ℕ) := by
    have : i = (i' : ℕ) + 2 * (i / 2) := by rw [hi'def]; simp only [Fin.val_mk]; omega
    conv_lhs => rw [this]
    exact CerednikDrinfeld.FormalODModule.gradedPiece_add_two_mul Φ _ _ _

  have hDV : ∀ m : CartierModule p Φ.F, (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).verschiebung m = verschiebungInt m := fun _ => rfl
  have hDPi : ∀ m : CartierModule p Φ.F, (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).varpi m = endAct Φ.varpiEnd m := fun _ => rfl
  have hDpiece : ∀ (l : Fin 2) (m : CartierModule p Φ.F), m ∈ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).piece l ↔ m ∈ Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) (l : ℕ) :=
    fun _ _ => Iff.rfl

  have hVinj : Function.Injective (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).verschiebung := hγ.verschiebung_injective

  obtain ⟨a, d, xt, ut, vt, u't, mt, ε, hPiγ, hpε, hLε, hut, hPiu⟩ :=
    CerednikDrinfeld.GradedCartierModuleData.IsCartierLMap.exists_smul_apply_eq_nMk_of_torsionFree
      p jS hS Dl γl hγl Ll hLl i'

  have hPiγ' : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).varpi (f (γl i')) = WittVector.teichmuller p (φ a) • f (γl (i' + 1)) + (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).verschiebung (f xt) := by
    rw [← hfPi, hPiγ, map_add, hsemi, WittVector.map_teichmuller, hfV]

  have hγi_mem : f (γl i') ∈ Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) i := by rw [hpiece_eq]; exact (hDpiece _ _).1 (hγ.1 i')
  obtain ⟨g, hg⟩ := hi _ hγi_mem
  have hφa : φ a = 0 ∧ f xt = g := by

    have key := teichmuller_coeff_unique (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ) hγ (Pi.single (i' + 1) (φ a) : Fin 2 → WittVector p k ⧸ pIdeal p (WittVector p k)) 0 (f xt) g ?_
    · refine ⟨?_, key.2⟩
      have := congrFun key.1 (i' + 1)
      simpa using this
    · have lhs : (∑ l : Fin 2, WittVector.teichmuller p ((Pi.single (i' + 1) (φ a) : Fin 2 → WittVector p k ⧸ pIdeal p (WittVector p k)) l) • f (γl l)) =
          WittVector.teichmuller p (φ a) • f (γl (i' + 1)) := by
        rw [Finset.sum_eq_single (i' + 1)]
        · rw [Pi.single_eq_same]
        · intro l _ hl
          rw [Pi.single_eq_of_ne hl, WittVector.teichmuller_zero, zero_smul]
        · intro h
          exact absurd (Finset.mem_univ _) h
      rw [lhs, ← hPiγ']
      have rhs : (∑ l : Fin 2, WittVector.teichmuller p ((0 : Fin 2 → WittVector p k ⧸ pIdeal p (WittVector p k)) l) • f (γl l)) = 0 := by
        refine Finset.sum_eq_zero fun l _ => ?_
        rw [Pi.zero_apply, WittVector.teichmuller_zero, zero_smul]
      rw [rhs, zero_add, hDV, hg, hDPi]

  have hεφ : WittVector.map φ ε = 1 := by
    have h := congrArg (WittVector.map φ) hpε
    rw [map_natCast, map_add, WittVector.map_teichmuller, map_natCast,
      natCast_eq_verschiebung_one (p := p), WittVector.map_verschiebung] at h
    have hp0 : ((p : ℕ) : WittVector p k ⧸ pIdeal p (WittVector p k)) = 0 := CharP.cast_eq_zero _ p
    rw [hp0, WittVector.teichmuller_zero, zero_add] at h
    exact (verschiebung_injective h).symm

  have hnMap_smul : ∀ (w : WittVector p S) (z : Dl.NMod),
      Dl.nMap (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ) f hfV hfPi (w • z) = WittVector.map φ w • Dl.nMap (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ) f hfV hfPi z := by
    intro w z
    obtain ⟨⟨m, m'⟩, rfl⟩ := Dl.nMk_surjective z
    rw [smul_nMk, nMap_nMk, nMap_nMk, smul_nMk, hsemi, hsemi, map_frobenius']

  have hLγ : L (f (γl i')) = (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk (f xt, 0) := by
    have h1 : L (f (γl i')) = Dl.nMap (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ) f hfV hfPi (ε • Ll (γl i')) := by
      rw [hnMap_smul, hεφ, one_smul, hpush]
    rw [h1, hLε, nMap_nMk, map_add]

    have hfu : f ut = (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).verschiebung (f u't) := by
      rw [hut, map_add, hsemi, WittVector.map_teichmuller, map_mul, map_pow, hφa.1,
        zero_pow (Nat.sub_ne_zero_of_lt (Fact.out : p.Prime).one_lt), zero_mul, WittVector.teichmuller_zero,
        zero_smul, zero_add, hfV]
    have hsum : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).varpi (f ut) + (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).verschiebung (f vt) = 0 := by
      rw [← hfPi, ← hfV, ← map_add, hPiu, hsemi, WittVector.map_teichmuller, hφa.1, WittVector.teichmuller_zero,
        zero_smul]
    have hfv : f vt = -(Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).varpi (f u't) := by
      rw [hfu, (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).varpi_verschiebung, ← map_add] at hsum
      have : f u't |> (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).varpi |> fun t => t + f vt = 0 := hVinj (by rw [map_zero]; exact hsum)
      exact eq_neg_of_add_eq_zero_right this
    rw [hfu, hfv]
    have : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk (f xt + (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).verschiebung (f u't), -(Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).varpi (f u't)) =
        (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk (f xt, 0) + (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).verschiebung (f u't), -(Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).varpi (f u't)) := by
      rw [← map_add, Prod.mk_add_mk, zero_add]
    rw [this, nMk_verschiebung_neg_varpi, add_zero]

  have hx' : x ∈ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).piece i' := (hDpiece _ _).2 (hpiece_eq ▸ hx)
  obtain ⟨c, m, hxcm⟩ := exists_eq_teichmuller_smul_add_verschiebung (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ) hγ i' x hx'

  have hyγ : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).verschiebung (f xt) = (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).varpi (f (γl i')) := by
    rw [hDV, hDPi, hφa.2]; exact hg
  have hy' : y = WittVector.frobenius (WittVector.teichmuller p c) • f xt + (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).varpi m := by
    apply hVinj
    rw [map_add, hDV y, hy, ← hDPi, hxcm, map_add, map_smul, ← hyγ, (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).smul_verschiebung,
      (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).varpi_verschiebung]
  rw [hy', hxcm, map_add, hL.isCartierLMap.map_smul, hLγ, hL.isCartierLMap.map_verschiebung, smul_nMk,
    ← map_add, Prod.mk_add_mk, smul_zero, zero_add]

end S_CerednikDrinfeld_FormalODModule_isCanonicalLMap_apply_eq_nMk_of_verschiebungInt_eq_endAct_varpiEnd
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_isCanonicalLMap_apply_eq_nMk_of_verschiebungInt_eq_endAct_varpiEnd (solution)
