-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_isCartierQuadruple_map_line_eq_of_edge_isogeny_of_apply_xi_eq_zero_of_apply_eta_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/6b8df871-a617-5a1c-aabf-2a67b5a0d3ba

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Definitions.Def_CerednikDrinfeld_EdgeFamilyConstants
import Theorems.Thm_CerednikDrinfeld_FormalODModule_finite_and_projective_kerAlgebra_of_X_pow_mem
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_X_pow_mem_span_of_hasKernelOfDegree
import Theorems.Thm_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_comp
import Theorems.Thm_CerednikDrinfeld_FormalODModule_hasKernelOfDegree_map
import Theorems.Thm_CerednikDrinfeld_FormalODModule_hasKernelOfDegree_of_span_range_eq
import Theorems.Thm_MvPowerSeries_free_and_finite_and_finrank_quotient_span_range_X_pow
import Theorems.Thm_MvPowerSeries_finrank_quotient_map_eq_of_ker_le
import Theorems.Thm_CerednikDrinfeld_EdgeFamily_edgeRingCharP_exists_ker_le_and_forall_ker_le_of_apply_eq_zero
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_hom_map_eq_add_verschiebungInt_of_endAct_varpiEnd_eq_teichmuller
import Theorems.Thm_MvPowerSeries_span_range_X_eq_ker_constantCoeff
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_hom_map_eq_of_endAct_varpiEnd_eq_verschiebungInt
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Theorems.Thm_MvFormalGroup_CartierModule_existsUnique_addMonoidHom_apply_eq_of_frobenius_expansion
import Theorems.Thm_MvFormalGroup_CartierModule_exists_hom_forall_map_eq_of_algebra_padicInt
import Theorems.Thm_MvFormalGroup_CartierModule_eq_of_forall_map_eq_of_algebra_padicInt
import Theorems.Thm_MvFormalGroup_CartierModule_verschiebungInt_injective_of_algebra_padicInt
import Theorems.Thm_MvFormalGroup_CartierModule_existsUnique_eq_sum_verschiebungInt_iterate_homothety_add
import Theorems.Thm_MvFormalGroup_CartierModule_existsUnique_forall_eq_sum_range_verschiebungInt_iterate_add
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Theorems.Thm_CerednikDrinfeld_EdgeFamily_edgeRingCharP_eq_comp_of_apply_xi_eq_zero_of_apply_eta_eq_zero
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsIsomorphic_map_ringHom
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_of_isIsomorphic
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsAdmissible_map_ringHom
import Theorems.Thm_CerednikDrinfeld_FormalODModule_endAct_varpiEnd_eq_teichmuller_sub_smul_add_verschiebungInt_of_hasStructureConstants_edgeConstants
import Theorems.Thm_CerednikDrinfeld_FormalODModule_forall_isCartierQuadruple_map_node_line_eq_of_rigidNum_single_eq
import Theorems.Thm_CerednikDrinfeld_FormalODModule_IsSpecial_map
import Theorems.Thm_WittVector_nonempty_ringEquiv_quotient_pIdeal_of_perfectRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_isCartierQuadruple_map_line_eq_of_edge_isogeny_of_apply_xi_eq_zero_of_apply_eta_eq_zero
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.mk.injEq CerednikDrinfeld.SpecialFormal.ModuliPackage.G_map CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.mk.sizeOf_spec CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.map_ψ CerednikDrinfeld.SpecialFormal.ModuliPackage.G_obj"

set_option autoImplicit false

universe u

open MvFormalGroup MvFormalGroup.CartierModule

namespace B29CMU

variable {p : ℕ} [hp : Fact p.Prime]

@[reducible] noncomputable def algebraPadicInt {B : Type u} [CommRing B] (j : CerednikDrinfeld.Zp2 p →+* B) :
    Algebra (PadicInt p) B :=
  (j.comp ((WittVector.map (algebraMap (ZMod p) (GaloisField p 2))).comp
    (WittVector.equiv p).symm.toRingHom)).toAlgebra

section generic

variable {R : Type u} [CommRing R] {d d' : ℕ} {Φ : MvFormalGroup d R} {Φ' : MvFormalGroup d' R}
  [Φ.IsComm] [Φ'.IsComm]

local notation "VV" => (verschiebungInt : CartierModule p Φ →+ CartierModule p Φ)
local notation "VV'" => (verschiebungInt : CartierModule p Φ' →+ CartierModule p Φ')

theorem eq_zero_of_forall_exists_iterate (x : CartierModule p Φ)
    (hx : ∀ N : ℕ, ∃ t : CartierModule p Φ, x = (⇑VV)^[N] t) : x = 0 := by
  have h := existsUnique_forall_eq_sum_range_verschiebungInt_iterate_add p Φ (fun _ => 0)
  refine h.unique ?_ ?_
  · intro N
    obtain ⟨t, ht⟩ := hx N
    exact ⟨t, by simpa [Function.iterate_fixed (map_zero _)] using ht⟩
  · intro N
    exact ⟨0, by simp [Function.iterate_fixed (map_zero _)]⟩

theorem eq_of_forall_sub_mem (x y : CartierModule p Φ)
    (h : ∀ N : ℕ, ∃ t : CartierModule p Φ, x - y = (⇑VV)^[N] t) : x = y :=
  sub_eq_zero.mp (eq_zero_of_forall_exists_iterate (x - y) h)

noncomputable def iterV (N : ℕ) : CartierModule p Φ →+ CartierModule p Φ where
  toFun := (⇑VV)^[N]
  map_zero' := Function.iterate_fixed (map_zero _) N
  map_add' a b := by
    induction N generalizing a b with
    | zero => rfl
    | succ N ih => simp only [Function.iterate_succ_apply', ih, map_add]

@[scoped simp] theorem iterV_apply (N : ℕ) (a : CartierModule p Φ) : iterV (p := p) (Φ := Φ) N a = (⇑VV)^[N] a :=
  rfl

theorem iterate_V_sub (N : ℕ) (a b : CartierModule p Φ) :
    (⇑VV)^[N] a - (⇑VV)^[N] b = (⇑VV)^[N] (a - b) := by
  rw [← iterV_apply, ← iterV_apply, ← iterV_apply, map_sub]

theorem iterate_V_add (N : ℕ) (a b : CartierModule p Φ) :
    (⇑VV)^[N] a + (⇑VV)^[N] b = (⇑VV)^[N] (a + b) := by
  rw [← iterV_apply, ← iterV_apply, ← iterV_apply, map_add]

theorem iterate_V_nsmul (N n : ℕ) (a : CartierModule p Φ) :
    n • (⇑VV)^[N] a = (⇑VV)^[N] (n • a) := by
  rw [← iterV_apply, ← iterV_apply, map_nsmul]

theorem iterate_V_sum {ι : Type*} (s : Finset ι) (N : ℕ) (a : ι → CartierModule p Φ) :
    ∑ i ∈ s, (⇑VV)^[N] (a i) = (⇑VV)^[N] (∑ i ∈ s, a i) := by
  simp only [← iterV_apply, map_sum]

theorem iterate_V_comm (N m : ℕ) (a : CartierModule p Φ) :
    (⇑VV)^[m] ((⇑VV)^[N] a) = (⇑VV)^[N] ((⇑VV)^[m] a) := by
  rw [← Function.iterate_add_apply, ← Function.iterate_add_apply, Nat.add_comm]

theorem homothety_iterate_V (N : ℕ) (b : R) (a : CartierModule p Φ) :
    homothety b ((⇑VV)^[N] a) = (⇑VV)^[N] (homothety (b ^ p ^ N) a) := by
  induction N generalizing b a with
  | zero => simp
  | succ N ih =>
    rw [Function.iterate_succ_apply', homothety_verschiebungInt, ih, Function.iterate_succ_apply',
      ← pow_mul, ← pow_succ']

theorem map_iterate_V (θ : CartierModule p Φ →+ CartierModule p Φ')
    (hV : ∀ f, θ (verschiebungInt f) = verschiebungInt (θ f)) (N : ℕ) (f : CartierModule p Φ) :
    θ ((⇑VV)^[N] f) = (⇑VV')^[N] (θ f) := by
  induction N generalizing f with
  | zero => rfl
  | succ N ih => rw [Function.iterate_succ_apply', hV, ih, Function.iterate_succ_apply']

theorem map_expansion {ι : Type*} [Fintype ι] (θ : CartierModule p Φ →+ CartierModule p Φ')
    (hV : ∀ f, θ (verschiebungInt f) = verschiebungInt (θ f))
    (hH : ∀ (b : R) f, θ (homothety b f) = homothety b (θ f))
    (N : ℕ) (c : Fin N → ι → R) (γ : ι → CartierModule p Φ) (h : CartierModule p Φ) :
    θ ((∑ m : Fin N, (⇑VV)^[(m : ℕ)] (∑ k : ι, homothety (c m k) (γ k))) + (⇑VV)^[N] h) =
      (∑ m : Fin N, (⇑VV')^[(m : ℕ)] (∑ k : ι, homothety (c m k) (θ (γ k)))) +
        (⇑VV')^[N] (θ h) := by
  simp only [map_add, map_sum, map_iterate_V θ hV, hH]

end generic

section main

variable {B : Type u} [CommRing B]

theorem intertwine [Algebra (PadicInt p) B] {d d' : ℕ} {Φ : MvFormalGroup d B} {Φ' : MvFormalGroup d' B}
    [Φ.IsComm] [Φ'.IsComm]
    (θ : CartierModule p Φ →+ CartierModule p Φ')
    (hθV : ∀ f, θ (verschiebungInt f) = verschiebungInt (θ f))
    (hθH : ∀ (b : B) f, θ (homothety b f) = homothety b (θ f))
    (hθF : ∀ f, θ (frobenius f) = frobenius (θ f))
    (γ : Fin d → CartierModule p Φ)
    (hγ : IsUnit (Matrix.of fun i j => tangent (γ i) j).det)
    (c : ℕ → Fin d → Fin d → B)
    (hF : ∀ (i : Fin d) (N : ℕ), ∃ h : CartierModule p Φ, frobenius (γ i) =
        (∑ m : Fin N, (⇑(verschiebungInt (p := p) (Φ := Φ)))^[(m : ℕ)]
          (∑ k : Fin d, homothety (c m i k) (γ k))) +
        (⇑(verschiebungInt (p := p) (Φ := Φ)))^[N] h)
    (e : MvFormalGroup.End Φ) (e' : MvFormalGroup.End Φ')
    (he : ∀ i, θ (endAct e (γ i)) = endAct e' (θ (γ i))) :
    ∀ f, θ (endAct e f) = endAct e' (θ f) := by
  set δ : Fin d → CartierModule p Φ' := fun i => θ (endAct e (γ i)) with hδ
  set ψ₁ : CartierModule p Φ →+ CartierModule p Φ' := θ.comp (endAct e) with hψ₁
  set ψ₂ : CartierModule p Φ →+ CartierModule p Φ' := (endAct e' : _ →+ _).comp θ with hψ₂
  have h1V : ∀ f, ψ₁ (verschiebungInt f) = verschiebungInt (ψ₁ f) := fun f => by
    show θ (endAct e (verschiebungInt f)) = verschiebungInt (θ (endAct e f))
    rw [endAct_verschiebungInt, hθV]
  have h1H : ∀ (b : B) f, ψ₁ (homothety b f) = homothety b (ψ₁ f) := fun b f => by
    show θ (endAct e (homothety b f)) = homothety b (θ (endAct e f))
    rw [endAct_homothety, hθH]
  have h1F : ∀ f, ψ₁ (frobenius f) = frobenius (ψ₁ f) := fun f => by
    show θ (endAct e (frobenius f)) = frobenius (θ (endAct e f))
    rw [endAct_frobenius, hθF]
  have h2V : ∀ f, ψ₂ (verschiebungInt f) = verschiebungInt (ψ₂ f) := fun f => by
    show endAct e' (θ (verschiebungInt f)) = verschiebungInt (endAct e' (θ f))
    rw [hθV, endAct_verschiebungInt]
  have h2H : ∀ (b : B) f, ψ₂ (homothety b f) = homothety b (ψ₂ f) := fun b f => by
    show endAct e' (θ (homothety b f)) = homothety b (endAct e' (θ f))
    rw [hθH, endAct_homothety]
  have h2F : ∀ f, ψ₂ (frobenius f) = frobenius (ψ₂ f) := fun f => by
    show endAct e' (θ (frobenius f)) = frobenius (endAct e' (θ f))
    rw [hθF, endAct_frobenius]
  have hFδ : ∀ (i : Fin d) (N : ℕ), ∃ h : CartierModule p Φ', frobenius (δ i) =
      (∑ m : Fin N, (⇑(verschiebungInt (p := p) (Φ := Φ')))^[(m : ℕ)]
        (∑ k : Fin d, homothety (c m i k) (δ k))) +
      (⇑(verschiebungInt (p := p) (Φ := Φ')))^[N] h := by
    intro i N
    obtain ⟨h, hh⟩ := hF i N
    refine ⟨ψ₁ h, ?_⟩
    have key := congrArg ψ₁ hh
    rw [h1F, map_expansion ψ₁ h1V h1H] at key
    exact key
  have hU := (existsUnique_addMonoidHom_apply_eq_of_frobenius_expansion p Φ Φ' γ hγ δ c hF hFδ).unique
    (y₁ := ψ₁) (y₂ := ψ₂) ⟨fun i => rfl, h1V, h1H, h1F⟩
    ⟨fun i => (he i).symm, h2V, h2H, h2F⟩
  intro f
  exact congrArg (fun ψ : CartierModule p Φ →+ CartierModule p Φ' => ψ f) hU

open CerednikDrinfeld in
theorem endAct_actEnd_mul (X : FormalODModule p B) (a b : Zp2 p) (f : CartierModule p X.F) :
    endAct (X.actEnd (a * b)) f = endAct (X.actEnd a) (endAct (X.actEnd b) f) := by
  have h : X.actEnd (a * b) = X.actEnd a * X.actEnd b := X.actRingHom.map_mul a b
  rw [h, map_mul]
  rfl

open CerednikDrinfeld in
theorem endAct_actEnd_add (X : FormalODModule p B) (a b : Zp2 p) (f : CartierModule p X.F) :
    endAct (X.actEnd (a + b)) f = endAct (X.actEnd a) f + endAct (X.actEnd b) f := by
  have h : X.actEnd (a + b) = X.actEnd a + X.actEnd b := X.actRingHom.map_add a b
  rw [h, map_add]
  rfl

open CerednikDrinfeld in
theorem endAct_actEnd_natCast (X : FormalODModule p B) (n : ℕ) (f : CartierModule p X.F) :
    endAct (X.actEnd (n : Zp2 p)) f = n • f := by
  have h : X.actEnd (n : Zp2 p) = (n : MvFormalGroup.End X.F) := map_natCast X.actRingHom n
  rw [h, endAct_natCast]

theorem witt_decompose {k : Type*} [CommRing k] [CharP k p] [PerfectRing k p] (x : WittVector p k) :
    ∃ x' : WittVector p k, x = WittVector.teichmuller p (x.coeff 0) + (p : WittVector p k) * x' := by
  set y : WittVector p k := x - WittVector.teichmuller p (x.coeff 0) with hy
  have hy0 : y.coeff 0 = 0 := by
    have h1 := (WittVector.constantCoeff : WittVector p k →+* k).map_sub x
      (WittVector.teichmuller p (x.coeff 0))
    simp only [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero, sub_self] at h1
    rw [hy]; exact h1
  have hyV : WittVector.verschiebung (y.shift 1) = y := by
    rw [WittVector.verschiebung_shift y 0 (fun i hi => by
      have : i = 0 := by omega
      subst this; exact hy0)]
    ext n; simp [WittVector.shift_coeff]
  refine ⟨(WittVector.frobeniusEquiv p k).symm (y.shift 1), ?_⟩
  have hfr : WittVector.frobenius ((WittVector.frobeniusEquiv p k).symm (y.shift 1)) = y.shift 1 :=
    (WittVector.frobeniusEquiv p k).apply_symm_apply (y.shift 1)
  rw [mul_comm, ← WittVector.verschiebung_frobenius, hfr, hyV, hy, add_sub_cancel]

open CerednikDrinfeld in

noncomputable def defect (X X' : FormalODModule p B)
    (θ : CartierModule p X.F →+ CartierModule p X'.F) (cc : Zp2 p) :
    CartierModule p X.F →+ CartierModule p X'.F :=
  θ.comp (endAct (X.actEnd cc) : CartierModule p X.F →+ CartierModule p X.F) -
    (endAct (X'.actEnd cc) : CartierModule p X'.F →+ CartierModule p X'.F).comp θ

open CerednikDrinfeld in
theorem defect_apply (X X' : FormalODModule p B)
    (θ : CartierModule p X.F →+ CartierModule p X'.F) (cc : Zp2 p) (f : CartierModule p X.F) :
    defect X X' θ cc f = θ (endAct (X.actEnd cc) f) - endAct (X'.actEnd cc) (θ f) := rfl

section defect

open CerednikDrinfeld

variable (X X' : FormalODModule p B) (θ : CartierModule p X.F →+ CartierModule p X'.F)
  (hθV : ∀ f, θ (verschiebungInt f) = verschiebungInt (θ f))
  (hθH : ∀ (b : B) f, θ (homothety b f) = homothety b (θ f))

include hθV in
theorem defect_V (cc : Zp2 p) (f : CartierModule p X.F) :
    defect X X' θ cc (verschiebungInt f) = verschiebungInt (defect X X' θ cc f) := by
  rw [defect_apply, defect_apply, endAct_verschiebungInt, hθV, hθV, endAct_verschiebungInt, map_sub]

include hθH in
theorem defect_H (cc : Zp2 p) (b : B) (f : CartierModule p X.F) :
    defect X X' θ cc (homothety b f) = homothety b (defect X X' θ cc f) := by
  rw [defect_apply, defect_apply, endAct_homothety, hθH, hθH, endAct_homothety, map_sub]

theorem defect_step (hT : ∀ (ζ : GaloisField p 2) (f : CartierModule p X.F),
      defect X X' θ (WittVector.teichmuller p ζ) f = 0) (cc : Zp2 p) :
    ∃ cc' : Zp2 p, ∀ f : CartierModule p X.F, defect X X' θ cc f = p • defect X X' θ cc' f := by
  obtain ⟨cc', hcc⟩ := witt_decompose (p := p) cc
  refine ⟨cc', fun f => ?_⟩
  have h0 := hT (cc.coeff 0) f
  rw [defect_apply, sub_eq_zero] at h0
  rw [defect_apply, defect_apply, hcc, endAct_actEnd_add, endAct_actEnd_add, map_add, endAct_actEnd_mul,
    endAct_actEnd_mul, endAct_actEnd_natCast, endAct_actEnd_natCast, map_nsmul, smul_sub, h0]
  abel

theorem defect_steps (hT : ∀ (ζ : GaloisField p 2) (f : CartierModule p X.F),
      defect X X' θ (WittVector.teichmuller p ζ) f = 0) (K : ℕ) (cc : Zp2 p) :
    ∃ cc' : Zp2 p, ∀ f : CartierModule p X.F, defect X X' θ cc f = p ^ K • defect X X' θ cc' f := by
  induction K generalizing cc with
  | zero => exact ⟨cc, fun f => by rw [pow_zero, one_smul]⟩
  | succ K ih =>
    obtain ⟨c₁, h₁⟩ := ih cc
    obtain ⟨c₂, h₂⟩ := defect_step X X' θ hT c₁
    exact ⟨c₂, fun f => by rw [h₁, h₂, smul_smul, ← pow_succ]⟩

end defect

theorem exists_eq_verschiebungInt_of_tangent_eq_zero [Algebra (PadicInt p) B] {d : ℕ}
    {Φ : MvFormalGroup d B} [Φ.IsComm] (γ : Fin d → CartierModule p Φ)
    (hγ : IsUnit (Matrix.of fun i j => tangent (γ i) j).det)
    (y : CartierModule p Φ) (hy : tangent y = 0) : ∃ t, y = verschiebungInt t := by
  obtain ⟨⟨e, t⟩, het, -⟩ := existsUnique_eq_sum_verschiebungInt_iterate_homothety_add p Φ γ hγ y 1
  have het' : y = (∑ k : Fin d, homothety (e 0 k) (γ k)) + verschiebungInt t := by
    simpa [Fin.sum_univ_one] using het
  have htan : ∀ jj : Fin d, ∑ k : Fin d, e 0 k * tangent (γ k) jj = 0 := by
    intro jj
    have h1 := congrArg (fun v : Fin d → B => v jj) (congrArg tangent het')
    simp only [hy, map_add, map_sum, tangent_homothety, tangent_verschiebungInt, add_zero,
      Pi.zero_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1
    exact h1.symm
  have hvec : Matrix.vecMul (e 0) (Matrix.of fun i j => tangent (γ i) j) = 0 := by
    funext jj
    exact htan jj
  have he0 : e 0 = 0 := by
    have h2 := congrArg (fun v => Matrix.vecMul v (Matrix.of fun i j => tangent (γ i) j)⁻¹) hvec
    rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hγ, Matrix.vecMul_one, Matrix.zero_vecMul] at h2
    exact h2
  refine ⟨t, ?_⟩
  rw [het']
  simp [he0, homothety_zero_left]

section claim

open CerednikDrinfeld

variable [Algebra (PadicInt p) B] (X X' : FormalODModule p B)
  (θ : CartierModule p X.F →+ CartierModule p X'.F)
  (hθV : ∀ f, θ (verschiebungInt f) = verschiebungInt (θ f))
  (hθH : ∀ (b : B) f, θ (homothety b f) = homothety b (θ f))
  (hsep : IsHausdorff (Ideal.span {(p : B)}) B)
  (γ : Fin 2 → CartierModule p X.F) (γ' : Fin 2 → CartierModule p X'.F)
  (hγ : IsUnit (Matrix.of fun i j => tangent (γ i) j).det)
  (hγ' : IsUnit (Matrix.of fun i j => tangent (γ' i) j).det)
  (hT : ∀ (ζ : GaloisField p 2) (f : CartierModule p X.F),
      defect X X' θ (WittVector.teichmuller p ζ) f = 0)

include hsep hγ' hT in

theorem defect_basis_succ (N : ℕ)
    (ih : ∀ (cc : Zp2 p) (f : CartierModule p X.F), ∃ y,
      defect X X' θ cc f = (⇑(verschiebungInt (p := p) (Φ := X'.F)))^[N] y)
    (cc : Zp2 p) (k : Fin 2) :
    ∃ t, defect X X' θ cc (γ k) = (⇑(verschiebungInt (p := p) (Φ := X'.F)))^[N + 1] t := by
  have hVinj' := verschiebungInt_injective_of_algebra_padicInt p X'.F
  obtain ⟨y₀, hy₀⟩ := ih cc (γ k)
  have hdiv : ∀ K : ℕ, ∃ yK, y₀ = p ^ K • yK := by
    intro K
    obtain ⟨cc', hcc'⟩ := defect_steps X X' θ hT K cc
    obtain ⟨yK, hyK⟩ := ih cc' (γ k)
    refine ⟨yK, hVinj'.iterate N ?_⟩
    rw [← hy₀, hcc', hyK, iterate_V_nsmul]
  have htan : tangent y₀ = 0 := by
    funext jj
    refine IsHausdorff.haus hsep _ fun K => ?_
    obtain ⟨yK, hyK⟩ := hdiv K
    have hmem : (p : B) ^ K * tangent yK jj ∈ Ideal.span {(p : B)} ^ K :=
      Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self (p : B)) K)
    rw [SModEq.sub_mem, sub_zero, Ideal.smul_eq_mul, Ideal.mul_top, hyK, map_nsmul,
      Pi.smul_apply, nsmul_eq_mul, Nat.cast_pow]
    exact hmem
  obtain ⟨t, ht⟩ := exists_eq_verschiebungInt_of_tangent_eq_zero γ' hγ' y₀ htan
  exact ⟨t, by rw [hy₀, ht, ← Function.iterate_succ_apply]⟩

include hθV hθH hsep hγ hγ' hT in
theorem defect_mem (N : ℕ) :
    ∀ (cc : Zp2 p) (f : CartierModule p X.F), ∃ y,
      defect X X' θ cc f = (⇑(verschiebungInt (p := p) (Φ := X'.F)))^[N] y := by
  induction N with
  | zero => exact fun cc f => ⟨defect X X' θ cc f, rfl⟩
  | succ N ih =>
    intro cc f
    obtain ⟨⟨e, t⟩, het, -⟩ :=
      existsUnique_eq_sum_verschiebungInt_iterate_homothety_add p X.F γ hγ f (N + 1)
    choose tk htk using defect_basis_succ X X' θ hsep γ γ' hγ' hT N ih cc
    refine ⟨(∑ m : Fin (N + 1), (⇑(verschiebungInt (p := p) (Φ := X'.F)))^[(m : ℕ)]
        (∑ k : Fin 2, homothety (e m k ^ p ^ (N + 1)) (tk k))) + defect X X' θ cc t, ?_⟩
    have key := congrArg (defect X X' θ cc) het
    rw [map_expansion (defect X X' θ cc) (defect_V X X' θ hθV cc) (defect_H X X' θ hθH cc)] at key
    rw [key]
    simp only [htk, homothety_iterate_V, iterate_V_sum, iterate_V_comm (N + 1), iterate_V_add]

include hθV hθH hsep hγ hγ' hT in
theorem defect_eq_zero (cc : Zp2 p) (f : CartierModule p X.F) : defect X X' θ cc f = 0 :=
  eq_zero_of_forall_exists_iterate _ fun N => defect_mem X X' θ hθV hθH hsep γ γ' hγ hγ' hT N cc f

end claim

end main

end B29CMU
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_exists_isCartierQuadruple_map_line_eq_of_edge_isogeny_of_apply_xi_eq_zero_of_apply_eta_eq_zero.B29CMU"

namespace B29R1

open CerednikDrinfeld MvFormalGroup MvFormalGroup.CartierModule

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [CharP R p]
  (X : FormalODModule p R)

example (w : WittVector p R) (f : CartierModule p X.F) :
    w • verschiebungInt f = verschiebungInt (WittVector.frobenius w • f) := smul_verschiebungInt w f
example (w : WittVector p R) (f : CartierModule p X.F) :
    frobenius (w • f) = WittVector.frobenius w • frobenius f := frobenius_smul w f
example (w : WittVector p R) (f : CartierModule p X.F) :
    verschiebungInt (w • frobenius f) = WittVector.verschiebung w • f := verschiebungInt_smul_frobenius w f
example (f : CartierModule p X.F) : frobenius (verschiebungInt f) = (p : WittVector p R) • f := by
  rw [frobenius_verschiebungInt_eq_smul]
example (f : CartierModule p X.F) : endAct X.varpiEnd (endAct X.varpiEnd f) = (p : ℕ) • f :=
  FormalODModule.endAct_varpiEnd_endAct_varpiEnd X f
example (w : WittVector p R) (f : CartierModule p X.F) : endAct X.varpiEnd (w • f) = w • endAct X.varpiEnd f :=
  endAct_smul_witt X.varpiEnd w f
example (f : CartierModule p X.F) : endAct X.varpiEnd (verschiebungInt f) = verschiebungInt (endAct X.varpiEnd f) :=
  endAct_verschiebungInt X.varpiEnd f
example (f : CartierModule p X.F) : endAct X.varpiEnd (frobenius f) = frobenius (endAct X.varpiEnd f) :=
  endAct_frobenius X.varpiEnd f
example (f : CartierModule p X.F) : verschiebungInt (frobenius f) = (p : WittVector p R) • f := by
  rw [verschiebungInt_apply_eq_verschiebung, verschiebung_frobenius_eq_smul]

section Structural

variable (γ : Fin 2 → CartierModule p X.F) (u v : WittVector p R)
  (hPi0 : endAct X.varpiEnd (γ 0) = (WittVector.frobenius u - u) • γ 1 + verschiebungInt (γ 0))
  (hPi1 : endAct X.varpiEnd (γ 1) = (WittVector.frobenius v - v) • γ 0 + verschiebungInt (γ 1))
  (huv : ∀ a b : ℕ, ((⇑(WittVector.frobenius (p := p) (R := R)))^[a] u) * ((⇑(WittVector.frobenius (p := p) (R := R)))^[b] v) = 0)
  (hV : Function.Injective (verschiebungInt (p := p) (Φ := X.F)))

theorem cross11 (huv : ∀ a b : ℕ, ((⇑(WittVector.frobenius (p := p) (R := R)))^[a] u) *
      ((⇑(WittVector.frobenius (p := p) (R := R)))^[b] v) = 0) (a a' b b' : ℕ) :
    (((⇑(WittVector.frobenius (p := p) (R := R)))^[a] u) - ((⇑(WittVector.frobenius (p := p) (R := R)))^[a'] u)) *
      (((⇑(WittVector.frobenius (p := p) (R := R)))^[b] v) - ((⇑(WittVector.frobenius (p := p) (R := R)))^[b'] v)) = 0 := by
  rw [sub_mul, mul_sub, mul_sub, huv, huv, huv, huv]; simp

theorem VF_eq (f : CartierModule p X.F) : verschiebungInt (frobenius f) = (p : WittVector p R) • f := by
  rw [verschiebungInt_apply_eq_verschiebung, verschiebung_frobenius_eq_smul]

theorem pi_pi_eq (f : CartierModule p X.F) : endAct X.varpiEnd (endAct X.varpiEnd f) = verschiebungInt (frobenius f) := by
  rw [FormalODModule.endAct_varpiEnd_endAct_varpiEnd X f, VF_eq, natCast_smul_eq_nsmul']

include hPi0 hPi1 huv hV in

theorem frob_gamma0 :
    frobenius (γ 0) = (WittVector.frobenius (WittVector.frobenius u) - u) • γ 1 + verschiebungInt (γ 0) := by
  apply hV
  have h := pi_pi_eq X (γ 0)
  rw [hPi0, map_add, endAct_smul_witt, hPi1, endAct_verschiebungInt, hPi0, smul_add, ← mul_smul,
    show (WittVector.frobenius u - u) * (WittVector.frobenius v - v) = 0 from by
      simpa using cross11 (p := p) u v huv 1 0 1 0,
    zero_smul, zero_add, smul_verschiebungInt, map_add] at h
  have hs : WittVector.frobenius (WittVector.frobenius u - u) + (WittVector.frobenius u - u) =
      WittVector.frobenius (WittVector.frobenius u) - u := by rw [map_sub]; abel
  rw [← h, ← map_add, ← map_add, ← add_assoc, ← add_smul, hs]

include hPi0 hPi1 huv hV in

theorem frob_gamma1 :
    frobenius (γ 1) = (WittVector.frobenius (WittVector.frobenius v) - v) • γ 0 + verschiebungInt (γ 1) := by
  apply hV
  have h := pi_pi_eq X (γ 1)
  rw [hPi1, map_add, endAct_smul_witt, hPi0, endAct_verschiebungInt, hPi1, smul_add, ← mul_smul,
    show (WittVector.frobenius v - v) * (WittVector.frobenius u - u) = 0 from by
      rw [mul_comm]; simpa using cross11 (p := p) u v huv 1 0 1 0,
    zero_smul, zero_add, smul_verschiebungInt, map_add] at h
  have hs : WittVector.frobenius (WittVector.frobenius v - v) + (WittVector.frobenius v - v) =
      WittVector.frobenius (WittVector.frobenius v) - v := by rw [map_sub]; abel
  rw [← h, ← map_add, ← map_add, ← add_assoc, ← add_smul, hs]

omit hV in
theorem core (g0 g1 : CartierModule p X.F) (u v : WittVector p R)
    (hPg0 : endAct X.varpiEnd g0 = (WittVector.frobenius u - u) • g1 + verschiebungInt g0)
    (hPg1 : endAct X.varpiEnd g1 = (WittVector.frobenius v - v) • g0 + verschiebungInt g1)
    (hFg0 : frobenius g0 = (WittVector.frobenius (WittVector.frobenius u) - u) • g1 + verschiebungInt g0)
    (hFg1 : frobenius g1 = (WittVector.frobenius (WittVector.frobenius v) - v) • g0 + verschiebungInt g1)
    (huv : ∀ a b : ℕ, ((⇑(WittVector.frobenius (p := p) (R := R)))^[a] u) *
      ((⇑(WittVector.frobenius (p := p) (R := R)))^[b] v) = 0) :
    frobenius ((p : WittVector p R) • g0 - WittVector.frobenius u • verschiebungInt g1) =
      verschiebungInt ((p : WittVector p R) • g0 - WittVector.frobenius u • verschiebungInt g1) ∧
    endAct X.varpiEnd ((p : WittVector p R) • g0 - WittVector.frobenius u • verschiebungInt g1) =
      verschiebungInt ((p : WittVector p R) • g0 - WittVector.frobenius u • verschiebungInt g1) := by
  have hσp : WittVector.frobenius (p : WittVector p R) = p := map_natCast _ p

  have cx : ∀ a b b' : ℕ, ((⇑(WittVector.frobenius (p := p) (R := R)))^[a] u) *
      (((⇑(WittVector.frobenius (p := p) (R := R)))^[b] v) - ((⇑(WittVector.frobenius (p := p) (R := R)))^[b'] v)) = 0 := by
    intro a b b'; rw [mul_sub, huv, huv, sub_zero]
  have c10 : WittVector.frobenius u * (WittVector.frobenius (WittVector.frobenius v) - v) = 0 := cx 1 2 0
  have c21 : WittVector.frobenius (WittVector.frobenius u) * (WittVector.frobenius v - v) = 0 := cx 2 1 0
  have c11 : WittVector.frobenius u * (WittVector.frobenius v - v) = 0 := cx 1 1 0

  have e1 : (p : WittVector p R) • verschiebungInt g0 = verschiebungInt ((p : WittVector p R) • g0) := by
    rw [smul_verschiebungInt, hσp]
  have e2 : u • ((p : WittVector p R) • g1) =
      verschiebungInt (verschiebungInt (WittVector.frobenius (WittVector.frobenius u) • g1)) := by
    rw [← VF_eq X g1, hFg1, smul_verschiebungInt, smul_add, ← mul_smul, c10, zero_smul, zero_add, smul_verschiebungInt]
  have e3 : verschiebungInt (WittVector.frobenius u • verschiebungInt g1) =
      verschiebungInt (verschiebungInt (WittVector.frobenius (WittVector.frobenius u) • g1)) := by
    rw [smul_verschiebungInt]
  have e4 : (p : WittVector p R) • ((WittVector.frobenius (WittVector.frobenius u) - u) • g1) -
      WittVector.frobenius (WittVector.frobenius u) • ((p : WittVector p R) • g1) = -(u • ((p : WittVector p R) • g1)) := by
    have hring : (p : WittVector p R) * (WittVector.frobenius (WittVector.frobenius u) - u) -
        WittVector.frobenius (WittVector.frobenius u) * (p : WittVector p R) = -(u * (p : WittVector p R)) := by ring
    rw [smul_smul, smul_smul, smul_smul, ← sub_smul, hring, neg_smul]
  refine ⟨?_, ?_⟩
  ·
    rw [map_sub, map_sub, frobenius_smul, frobenius_smul, hσp, hFg0, frobenius_verschiebungInt_eq_smul, smul_add, e1,
      e3, ← e2]
    set A := verschiebungInt ((p : WittVector p R) • g0) with hA
    set B := u • ((p : WittVector p R) • g1) with hB
    set C := (p : WittVector p R) • ((WittVector.frobenius (WittVector.frobenius u) - u) • g1) with hC
    set D := WittVector.frobenius (WittVector.frobenius u) • ((p : WittVector p R) • g1) with hD
    have e4' : C - D = -B := e4
    calc C + A - D = A + (C - D) := by abel
      _ = A - B := by rw [e4']; abel
  ·
    rw [map_sub, map_sub, endAct_smul_witt, endAct_smul_witt, hPg0, endAct_verschiebungInt, hPg1, smul_add, e1,
      map_add, smul_add, e3]
    have z1 : WittVector.frobenius u • verschiebungInt ((WittVector.frobenius v - v) • g0) = 0 := by
      rw [smul_verschiebungInt, ← mul_smul, c21, zero_smul, map_zero]
    have e5 : (p : WittVector p R) • ((WittVector.frobenius u - u) • g1) =
        verschiebungInt (verschiebungInt (WittVector.frobenius (WittVector.frobenius (WittVector.frobenius u)) • g1)) -
          verschiebungInt (verschiebungInt (WittVector.frobenius (WittVector.frobenius u) • g1)) := by
      have c' : WittVector.frobenius (WittVector.frobenius u - u) * (WittVector.frobenius (WittVector.frobenius v) - v) = 0 := by
        rw [map_sub, sub_mul]
        have h1 : WittVector.frobenius (WittVector.frobenius u) * (WittVector.frobenius (WittVector.frobenius v) - v) = 0 := cx 2 2 0
        rw [h1, c10, sub_zero]
      rw [smul_smul, mul_comm, ← smul_smul, ← VF_eq X g1, hFg1, smul_verschiebungInt, smul_add, ← mul_smul, c',
        zero_smul, zero_add, smul_verschiebungInt, map_sub, map_sub, sub_smul, map_sub, map_sub]
    have e6 : WittVector.frobenius u • verschiebungInt (verschiebungInt g1) =
        verschiebungInt (verschiebungInt (WittVector.frobenius (WittVector.frobenius (WittVector.frobenius u)) • g1)) := by
      rw [smul_verschiebungInt, smul_verschiebungInt]
    rw [z1, zero_add, e5, e6]
    set A := verschiebungInt ((p : WittVector p R) • g0) with hA
    set P := verschiebungInt (verschiebungInt (WittVector.frobenius (WittVector.frobenius (WittVector.frobenius u)) • g1)) with hP
    set Q := verschiebungInt (verschiebungInt (WittVector.frobenius (WittVector.frobenius u) • g1)) with hQ
    abel

end Structural
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_exists_isCartierQuadruple_map_line_eq_of_edge_isogeny_of_apply_xi_eq_zero_of_apply_eta_eq_zero.B29CMU"

end B29R1
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_exists_isCartierQuadruple_map_line_eq_of_edge_isogeny_of_apply_xi_eq_zero_of_apply_eta_eq_zero.B29CMU"

namespace B29R1asm

open CerednikDrinfeld MvFormalGroup MvFormalGroup.CartierModule

variable {p : ℕ} [Fact p.Prime]

def toODHom {B : Type} [CommRing B] {X X' : FormalODModule p B} (φ : MvFormalGroup.Hom X.F X'.F)
    (hact : ∀ a, φ.comp (X.actEnd a) = (X'.actEnd a).comp φ)
    (hvarpi : φ.comp X.varpiEnd = X'.varpiEnd.comp φ) : X.Hom X' :=
  ⟨φ.toPowerSeries,
    ⟨CerednikDrinfeld.SpecialFormal.IsLawHom.of_hom φ,
      fun a => congrArg MvFormalGroup.Hom.toPowerSeries (hact a),
      congrArg MvFormalGroup.Hom.toPowerSeries hvarpi⟩⟩

theorem toODHom_toLawHom {B : Type} [CommRing B] {X X' : FormalODModule p B} (φ : MvFormalGroup.Hom X.F X'.F)
    (hact : ∀ a, φ.comp (X.actEnd a) = (X'.actEnd a).comp φ)
    (hvarpi : φ.comp X.varpiEnd = X'.varpiEnd.comp φ) : (toODHom φ hact hvarpi).toLawHom = φ :=
  MvFormalGroup.Hom.ext rfl

def nodeC (R : Type) [CommRing R] : ℕ → Fin 2 → Fin 2 → R := fun n i k => if n = 1 ∧ k = i then 1 else 0

theorem sum_nodeC {R : Type} [CommRing R] {d : ℕ} {Φ : MvFormalGroup d R} [Φ.IsComm]
    (x : Fin 2 → CartierModule p Φ) (i : Fin 2) (N : ℕ) :
    (∑ m : Fin N, (⇑(verschiebungInt (p := p) (Φ := Φ)))^[(m : ℕ)]
        (∑ k : Fin 2, homothety (nodeC R m i k) (x k))) =
      if 1 < N then verschiebungInt (x i) else 0 := by
  have hterm : ∀ m : Fin N, (⇑(verschiebungInt (p := p) (Φ := Φ)))^[(m : ℕ)]
      (∑ k : Fin 2, homothety (nodeC R m i k) (x k)) = if (m : ℕ) = 1 then verschiebungInt (x i) else 0 := by
    intro m
    by_cases hm : (m : ℕ) = 1
    · rw [if_pos hm, hm, Function.iterate_one]
      congr 1
      rw [Finset.sum_eq_single i]
      · simp [nodeC, homothety_one]
      · intro k _ hk; simp [nodeC, if_neg hk, homothety_zero_left]
      · intro h; exact absurd (Finset.mem_univ i) h
    · rw [if_neg hm]
      have : (∑ k : Fin 2, homothety (nodeC R m i k) (x k)) = 0 := by
        refine Finset.sum_eq_zero fun k _ => ?_
        simp [nodeC, hm, homothety_zero_left]
      rw [this]
      exact Function.iterate_fixed (map_zero _) _
  rw [Finset.sum_congr rfl fun m _ => hterm m]
  split_ifs with hN
  · rw [Finset.sum_eq_single (⟨1, hN⟩ : Fin N)]
    · simp
    · intro m _ hm
      rw [if_neg]
      intro h; exact hm (Fin.ext h)
    · intro h; exact absurd (Finset.mem_univ _) h
  · refine Finset.sum_eq_zero fun m _ => ?_
    rw [if_neg]; intro h; exact hN (h ▸ m.isLt)

theorem expansion_of_frobenius_eq {R : Type} [CommRing R] {d : ℕ} {Φ : MvFormalGroup d R} [Φ.IsComm]
    (x : Fin 2 → CartierModule p Φ) (i : Fin 2) (hx : frobenius (x i) = verschiebungInt (x i)) (N : ℕ) :
    ∃ h : CartierModule p Φ, frobenius (x i) =
      (∑ m : Fin N, (⇑(verschiebungInt (p := p) (Φ := Φ)))^[(m : ℕ)]
        (∑ k : Fin 2, homothety (nodeC R m i k) (x k))) +
      (⇑(verschiebungInt (p := p) (Φ := Φ)))^[N] h := by
  rw [sum_nodeC, hx]
  split_ifs with hN
  · exact ⟨0, by rw [Function.iterate_fixed (map_zero _) N, add_zero]⟩
  · rcases Nat.lt_or_ge N 1 with h0 | h1
    · have : N = 0 := by omega
      subst this
      exact ⟨verschiebungInt (x i), by simp⟩
    · have : N = 1 := by omega
      subst this
      exact ⟨x i, by simp⟩

end B29R1asm
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_exists_isCartierQuadruple_map_line_eq_of_edge_isogeny_of_apply_xi_eq_zero_of_apply_eta_eq_zero.B29CMU"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal MvFormalGroup MvFormalGroup.CartierModule

open scoped PadicInt Padic

namespace B30R1b

section chart
variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k]

scoped instance isNoetherianRing_edgeRingCharP : IsNoetherianRing (EdgeFamily.edgeRingCharP p k) :=
  IsLocalization.isNoetherianRing (Submonoid.powers (FormalOmega.edgeQuot.discr k (0 : k) p)) _
    (show IsNoetherianRing (MvPolynomial (Fin 2) k ⧸ Ideal.span {FormalOmega.edgeRel k (0 : k)}) from inferInstance)

theorem exists_nodePoint :
    ∃ f₀ : EdgeFamily.edgeRingCharP p k →+* k,
      f₀ (EdgeFamily.edgeRingCharP.ξ p k) = 0 ∧ f₀ (EdgeFamily.edgeRingCharP.η p k) = 0 := by
  have h1 : IsUnit ((0 : k) ^ (p - 1) - 1) := by
    rw [zero_pow (Nat.sub_ne_zero_of_lt (Fact.out : p.Prime).one_lt), zero_sub]; exact isUnit_one.neg
  let pt : (FormalOmega.chartE k (0 : k) p).obj k := ⟨((0 : k), (0 : k)), by simp, h1, h1⟩
  refine ⟨(FormalOmega.chartERing.lift pt).toRingHom, ?_, ?_⟩
  · exact FormalOmega.chartERing.lift_ξ pt
  · exact FormalOmega.chartERing.lift_η pt

end chart
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_exists_isCartierQuadruple_map_line_eq_of_edge_isogeny_of_apply_xi_eq_zero_of_apply_eta_eq_zero.B29CMU"

section series
variable {B : Type} [CommRing B]

theorem comp_mem_span (ψ φ : Series B) (hψ0 : ∀ i, MvPowerSeries.constantCoeff (ψ i) = 0)
    (hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) (i : Fin 2) :
    (ψ.comp φ) i ∈ Ideal.span (Set.range φ) := by
  have hsub := MvPowerSeries.hasSubst_of_constantCoeff_zero hφ0
  let F : MvPowerSeries (Fin 2) B →+* MvPowerSeries (Fin 2) B :=
    (MvPowerSeries.substAlgHom hsub : MvPowerSeries (Fin 2) B →ₐ[B] _).toRingHom
  have hF : ∀ g, F g = MvPowerSeries.subst φ g := fun g => by
    show (MvPowerSeries.substAlgHom hsub) g = _; rw [← MvPowerSeries.coe_substAlgHom hsub]
  have hc : ψ i ∈ Ideal.span (Set.range (MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) B)) := by
    rw [MvPowerSeries.span_range_X_eq_ker_constantCoeff, RingHom.mem_ker]; exact hψ0 i
  have h1 : (Ideal.span (Set.range (MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) B))).map F ≤ Ideal.span (Set.range φ) := by
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    rw [hF, MvPowerSeries.subst_X hsub]
    exact Ideal.subset_span ⟨j, rfl⟩
  have h2 := h1 (Ideal.mem_map_of_mem F hc)
  rw [hF] at h2
  exact h2

theorem X_pow_mem_of_comp (ψ φ : Series B) (hψ0 : ∀ i, MvPowerSeries.constantCoeff (ψ i) = 0)
    (hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0)
    (hN : ∃ N : ℕ, ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ N ∈ Ideal.span (Set.range (ψ.comp φ))) :
    ∃ N : ℕ, ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ N ∈ Ideal.span (Set.range φ) := by
  obtain ⟨N, hN⟩ := hN
  refine ⟨N, fun i => ?_⟩
  have hle : Ideal.span (Set.range (ψ.comp φ)) ≤ Ideal.span (Set.range φ) :=
    Ideal.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact comp_mem_span ψ φ hψ0 hφ0 j)
  exact hle (hN i)

theorem span_range_eq_span_X_of_comp_eq_id (ψ φ : Series B) (hψ0 : ∀ i, MvPowerSeries.constantCoeff (ψ i) = 0)
    (hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) (h : ψ.comp φ = Series.id B) :
    Ideal.span (Set.range φ) =
      Ideal.span (Set.range fun i : Fin 2 => (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ 1) := by
  have hX : (Set.range fun i : Fin 2 => (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ 1) =
      Set.range (MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) B) := by
    simp only [pow_one]
  rw [hX]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [MvPowerSeries.span_range_X_eq_ker_constantCoeff, SetLike.mem_coe, RingHom.mem_ker]
    exact hφ0 i
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    have := comp_mem_span ψ φ hψ0 hφ0 i
    rwa [h] at this

theorem hasKernelOfDegree_one_of_comp_eq_id (p : ℕ) [Fact p.Prime] [Nontrivial B] (ψ φ : Series B)
    (hψ0 : ∀ i, MvPowerSeries.constantCoeff (ψ i) = 0)
    (hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) (h : ψ.comp φ = Series.id B) :
    FormalODModule.HasKernelOfDegree φ (p ^ 0) := by
  have hI := span_range_eq_span_X_of_comp_eq_id ψ φ hψ0 hφ0 h
  obtain ⟨hfree, hfin, hrank⟩ := MvPowerSeries.free_and_finite_and_finrank_quotient_span_range_X_pow B 2 (fun _ => 1)
  refine CerednikDrinfeld.FormalODModule.hasKernelOfDegree_of_span_range_eq p φ _ 0 hI hfin
    (Module.Projective.of_free) (fun κ _ f => ?_)
  have hmap : (Ideal.span (Set.range fun i : Fin 2 => (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ 1)).map
      (MvPowerSeries.map f) = Ideal.span (Set.range fun i : Fin 2 => (MvPowerSeries.X i : MvPowerSeries (Fin 2) κ) ^ 1) := by
    have hfun : (⇑(MvPowerSeries.map f) ∘ fun i : Fin 2 => (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ 1) =
        fun i : Fin 2 => (MvPowerSeries.X i : MvPowerSeries (Fin 2) κ) ^ 1 := by
      funext i
      show MvPowerSeries.map f (MvPowerSeries.X i ^ 1) = MvPowerSeries.X i ^ 1
      rw [map_pow, MvPowerSeries.map_X]
    rw [Ideal.map_span, ← Set.range_comp, hfun]
  rw [hmap, (MvPowerSeries.free_and_finite_and_finrank_quotient_span_range_X_pow κ 2 (fun _ => 1)).2.2]
  simp

end series
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_exists_isCartierQuadruple_map_line_eq_of_edge_isogeny_of_apply_xi_eq_zero_of_apply_eta_eq_zero.B29CMU"

section uniq
open B29CMU B29R1 B29R1asm

theorem lawHom_eq_of_apply_basis {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [CharP R p] (j : Zp2 p →+* R)
    (Y : FormalODModule p R) {Φ' : MvFormalGroup 2 R} [Φ'.IsComm]
    (δ : Fin 2 → CartierModule p Y.F) (hδ : Y.IsHomogeneousVBasis j δ)
    (hδ0 : endAct Y.varpiEnd (δ 0) = verschiebungInt (δ 0))
    (hδ1 : endAct Y.varpiEnd (δ 1) = verschiebungInt (δ 1))
    (φ ψ : MvFormalGroup.Hom Y.F Φ') (h : ∀ i, CartierModule.map φ (δ i) = CartierModule.map ψ (δ i)) :
    φ = ψ := by
  letI : Algebra (PadicInt p) R := algebraPadicInt j
  have hVY := verschiebungInt_injective_of_algebra_padicInt p Y.F
  have h00 : ∀ a b : ℕ, ((⇑(WittVector.frobenius (p := p) (R := R)))^[a] (0 : WittVector p R)) *
      ((⇑(WittVector.frobenius (p := p) (R := R)))^[b] (0 : WittVector p R)) = 0 := by
    intro a b; rw [Function.iterate_fixed (map_zero _) a, zero_mul]
  have hδ0' : endAct Y.varpiEnd (δ 0) = (WittVector.frobenius (0 : WittVector p R) - 0) • δ 1 + verschiebungInt (δ 0) := by
    rw [map_zero, sub_zero, zero_smul, zero_add]; exact hδ0
  have hδ1' : endAct Y.varpiEnd (δ 1) = (WittVector.frobenius (0 : WittVector p R) - 0) • δ 0 + verschiebungInt (δ 1) := by
    rw [map_zero, sub_zero, zero_smul, zero_add]; exact hδ1
  have hFδ0 : frobenius (δ 0) = verschiebungInt (δ 0) := by
    have := frob_gamma0 Y δ 0 0 hδ0' hδ1' h00 hVY
    rwa [map_zero, map_zero, sub_zero, zero_smul, zero_add] at this
  have hFδ1 : frobenius (δ 1) = verschiebungInt (δ 1) := by
    have := frob_gamma1 Y δ 0 0 hδ0' hδ1' h00 hVY
    rwa [map_zero, map_zero, sub_zero, zero_smul, zero_add] at this
  have hFδ : ∀ i : Fin 2, frobenius (δ i) = verschiebungInt (δ i) := by
    intro i; fin_cases i
    · exact hFδ0
    · exact hFδ1
  set m : Fin 2 → CartierModule p Φ' := fun i => CartierModule.map φ (δ i) with hm
  have hFm : ∀ i : Fin 2, frobenius (m i) = verschiebungInt (m i) := fun i => by
    show frobenius (CartierModule.map φ (δ i)) = verschiebungInt (CartierModule.map φ (δ i))
    rw [← map_frobenius, hFδ, map_verschiebungInt]
  have hF : ∀ (i : Fin 2) (N : ℕ), ∃ h : CartierModule p Y.F, frobenius (δ i) =
      (∑ m' : Fin N, (⇑(verschiebungInt (p := p) (Φ := Y.F)))^[(m' : ℕ)]
        (∑ k : Fin 2, homothety (nodeC R m' i k) (δ k))) +
      (⇑(verschiebungInt (p := p) (Φ := Y.F)))^[N] h := fun i N => expansion_of_frobenius_eq δ i (hFδ i) N
  have hF' : ∀ (i : Fin 2) (N : ℕ), ∃ h : CartierModule p Φ', frobenius (m i) =
      (∑ m' : Fin N, (⇑(verschiebungInt (p := p) (Φ := Φ')))^[(m' : ℕ)]
        (∑ k : Fin 2, homothety (nodeC R m' i k) (m k))) +
      (⇑(verschiebungInt (p := p) (Φ := Φ')))^[N] h := fun i N => expansion_of_frobenius_eq m i (hFm i) N
  have key := (existsUnique_addMonoidHom_apply_eq_of_frobenius_expansion p Y.F Φ' δ hδ.2 m (nodeC R) hF hF').unique
    (y₁ := CartierModule.map φ) (y₂ := CartierModule.map ψ)
    ⟨fun i => rfl, fun f => map_verschiebungInt φ f, fun b f => map_homothety φ b f, fun f => map_frobenius φ f⟩
    ⟨fun i => (h i).symm, fun f => map_verschiebungInt ψ f, fun b f => map_homothety ψ b f, fun f => map_frobenius ψ f⟩
  exact eq_of_forall_map_eq_of_algebra_padicInt p Y.F Φ' φ ψ (fun f => by rw [key])

end uniq
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_exists_isCartierQuadruple_map_line_eq_of_edge_isogeny_of_apply_xi_eq_zero_of_apply_eta_eq_zero.B29CMU"

section compdual
open B29CMU B29R1 B29R1asm

theorem comp_dual_eq_act (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] [CharP R p] (j : Zp2 p →+* R)
    (ξ η : R) (hξη : ξ * η = 0)
    (Y X : FormalODModule p R)
    (δ : Fin 2 → CartierModule p Y.F) (hδ : Y.IsHomogeneousVBasis j δ)
    (hδ0 : endAct Y.varpiEnd (δ 0) = verschiebungInt (δ 0))
    (hδ1 : endAct Y.varpiEnd (δ 1) = verschiebungInt (δ 1))
    (γ : Fin 2 → CartierModule p X.F)
    (ρ : FormalODModule.Hom Y X)
    (hρ0 : CartierModule.map ρ.toLawHom (δ 0) =
      (p : WittVector p R) • γ 0 - verschiebungInt (WittVector.teichmuller p (η ^ p ^ 2) • γ 1))
    (hρ1 : CartierModule.map ρ.toLawHom (δ 1) =
      (p : WittVector p R) • γ 1 - verschiebungInt (WittVector.teichmuller p (ξ ^ p ^ 2) • γ 0))
    (ρd : FormalODModule.Hom X Y)
    (hρd0 : CartierModule.map ρd.toLawHom (γ 0) =
      (p : WittVector p R) • δ 0 + verschiebungInt (WittVector.teichmuller p (η ^ p ^ 2) • δ 1))
    (hρd1 : CartierModule.map ρd.toLawHom (γ 1) =
      (p : WittVector p R) • δ 1 + verschiebungInt (WittVector.teichmuller p (ξ ^ p ^ 2) • δ 0)) :
    ρd.toSeries.comp ρ.toSeries = Y.act ((p : Zp2 p) ^ 2) := by
  have hσp : WittVector.frobenius (p : WittVector p R) = p := map_natCast _ p
  have hcase : ∀ (a b : CartierModule p Y.F) (ga gb : CartierModule p X.F) (x y : R),
      x * y = 0 →
      CartierModule.map ρ.toLawHom a = (p : WittVector p R) • ga - verschiebungInt (WittVector.teichmuller p (y ^ p ^ 2) • gb) →
      CartierModule.map ρd.toLawHom ga = (p : WittVector p R) • a + verschiebungInt (WittVector.teichmuller p (y ^ p ^ 2) • b) →
      CartierModule.map ρd.toLawHom gb = (p : WittVector p R) • b + verschiebungInt (WittVector.teichmuller p (x ^ p ^ 2) • a) →
      CartierModule.map ρd.toLawHom (CartierModule.map ρ.toLawHom a) = (p ^ 2 : ℕ) • a := by
    intro a b ga gb x y hxy ha hga hgb
    have hteich0 : ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → WittVector.teichmuller p (y ^ m) * WittVector.teichmuller p (x ^ n) = 0 := by
      intro m n hm hn
      obtain ⟨m', rfl⟩ := Nat.exists_eq_add_of_le hm
      obtain ⟨n', rfl⟩ := Nat.exists_eq_add_of_le hn
      rw [← map_mul, pow_add, pow_add, pow_one, pow_one,
        show y * y ^ m' * (x * x ^ n') = (x * y) * (y ^ m' * x ^ n') by ring, hxy, zero_mul, WittVector.teichmuller_zero]
    have hteich : WittVector.teichmuller p ((y ^ p ^ 2) ^ p) * WittVector.teichmuller p (x ^ p ^ 2) = 0 := by
      rw [← pow_mul]
      exact hteich0 _ _ (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) (Fact.out : p.Prime).ne_zero))
        (Nat.one_le_pow _ _ (Fact.out : p.Prime).pos)
    have e1 : WittVector.teichmuller p (y ^ p ^ 2) • verschiebungInt (WittVector.teichmuller p (x ^ p ^ 2) • a) = 0 := by
      rw [smul_verschiebungInt, WittVector.frobenius_teichmuller_eq, ← mul_smul, hteich, zero_smul, map_zero]
    have e2 : WittVector.teichmuller p (y ^ p ^ 2) • ((p : WittVector p R) • b) =
        (p : WittVector p R) • (WittVector.teichmuller p (y ^ p ^ 2) • b) := by
      rw [← mul_smul, mul_comm, mul_smul]
    rw [ha, map_sub, map_smul_witt, map_verschiebungInt, map_smul_witt, hga, hgb,
      smul_add (WittVector.teichmuller p (y ^ p ^ 2)), e1, add_zero, e2,
      smul_add, smul_verschiebungInt (p : WittVector p R), hσp, add_sub_cancel_right,
      ← mul_smul, ← Nat.cast_mul, ← pow_two, natCast_smul_eq_nsmul']
  have hlaw : (ρd.comp ρ).toLawHom = Y.actEnd ((p : Zp2 p) ^ 2) := by
    refine lawHom_eq_of_apply_basis j Y δ hδ hδ0 hδ1 _ _ (fun i => ?_)
    have hc : (ρd.comp ρ).toLawHom = ρd.toLawHom.comp ρ.toLawHom := rfl
    rw [hc, CartierModule.map_comp,
      ← CartierModule.endAct_apply (Y.actEnd _), show ((p : Zp2 p) ^ 2) = ((p ^ 2 : ℕ) : Zp2 p) by push_cast; ring,
      endAct_actEnd_natCast]
    fin_cases i
    · exact hcase (δ 0) (δ 1) (γ 0) (γ 1) _ _ hξη hρ0 hρd0 hρd1
    · exact hcase (δ 1) (δ 0) (γ 1) (γ 0) _ _ (by rw [mul_comm]; exact hξη) hρ1 hρd1 hρd0
  exact congrArg MvFormalGroup.Hom.toPowerSeries hlaw

end compdual
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_exists_isCartierQuadruple_map_line_eq_of_edge_isogeny_of_apply_xi_eq_zero_of_apply_eta_eq_zero.B29CMU"

section node
open B29CMU B29R1 B29R1asm

theorem finrank_kerAlgebra_map_node (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] [IsNoetherianRing R] (j : Zp2 p →+* R)
    (ξ η : R) {κ : Type} [Field κ] [CharP κ p] (f₀ : R →+* κ) (hf₀ξ : f₀ ξ = 0) (hf₀η : f₀ η = 0)
    (Y X : FormalODModule p R) (hX4 : X.HasHeight 4)
    (δ : Fin 2 → CartierModule p Y.F) (hδ : Y.IsHomogeneousVBasis j δ)
    (hδ0 : endAct Y.varpiEnd (δ 0) = verschiebungInt (δ 0))
    (hδ1 : endAct Y.varpiEnd (δ 1) = verschiebungInt (δ 1))
    (γ : Fin 2 → CartierModule p X.F) (hγ : X.IsHomogeneousVBasis j γ)
    (hγ0 : endAct X.varpiEnd (γ 0) =
      (WittVector.teichmuller p (η ^ p) - WittVector.teichmuller p η) • γ 1 + verschiebungInt (γ 0))
    (hγ1 : endAct X.varpiEnd (γ 1) =
      (WittVector.teichmuller p (ξ ^ p) - WittVector.teichmuller p ξ) • γ 0 + verschiebungInt (γ 1))
    (ρ : FormalODModule.Hom Y X)
    (hρ0 : CartierModule.map ρ.toLawHom (δ 0) =
      (p : WittVector p R) • γ 0 - verschiebungInt (WittVector.teichmuller p (η ^ p ^ 2) • γ 1))
    (hρ1 : CartierModule.map ρ.toLawHom (δ 1) =
      (p : WittVector p R) • γ 1 - verschiebungInt (WittVector.teichmuller p (ξ ^ p ^ 2) • γ 0)) :
    Module.finrank κ (FormalODModule.KerAlgebra (ρ.toSeries.map f₀)) = p ^ 4 := by
  have hW0 : ∀ (x : R) (n : ℕ), f₀ x = 0 → 0 < n → WittVector.map f₀ (WittVector.teichmuller p (x ^ n)) = 0 := by
    intro x n hx hn
    rw [WittVector.map_teichmuller, map_pow, hx, zero_pow hn.ne', WittVector.teichmuller_zero]
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hδb := hδ.map f₀
  have hγb := hγ.map f₀
  have hδb0 : endAct (Y.map f₀).varpiEnd (baseChange f₀ (δ 0)) = verschiebungInt (baseChange f₀ (δ 0)) := by
    rw [← FormalODModule.baseChange_endAct_varpiEnd, hδ0, baseChangeEq_verschiebungInt]
  have hδb1 : endAct (Y.map f₀).varpiEnd (baseChange f₀ (δ 1)) = verschiebungInt (baseChange f₀ (δ 1)) := by
    rw [← FormalODModule.baseChange_endAct_varpiEnd, hδ1, baseChangeEq_verschiebungInt]
  have hγb0 : endAct (X.map f₀).varpiEnd (baseChange f₀ (γ 0)) = verschiebungInt (baseChange f₀ (γ 0)) := by
    rw [← FormalODModule.baseChange_endAct_varpiEnd, hγ0, map_add, baseChangeEq_smul_witt, baseChangeEq_verschiebungInt, map_sub,
      hW0 _ _ hf₀η hp0, show WittVector.teichmuller p η = WittVector.teichmuller p (η ^ 1) by rw [pow_one],
      hW0 _ _ hf₀η one_pos, sub_self, zero_smul, zero_add]
  have hγb1 : endAct (X.map f₀).varpiEnd (baseChange f₀ (γ 1)) = verschiebungInt (baseChange f₀ (γ 1)) := by
    rw [← FormalODModule.baseChange_endAct_varpiEnd, hγ1, map_add, baseChangeEq_smul_witt, baseChangeEq_verschiebungInt, map_sub,
      hW0 _ _ hf₀ξ hp0, show WittVector.teichmuller p ξ = WittVector.teichmuller p (ξ ^ 1) by rw [pow_one],
      hW0 _ _ hf₀ξ one_pos, sub_self, zero_smul, zero_add]
  set δb : Fin 2 → CartierModule p (Y.map f₀).F := fun i => baseChange f₀ (δ i) with hδbdef
  set γb : Fin 2 → CartierModule p (X.map f₀).F := fun i => baseChange f₀ (γ i) with hγbdef
  have hts : ∀ i, (ρ.map f₀).toLawHom.toPowerSeries i = MvPowerSeries.map f₀ (ρ.toLawHom.toPowerSeries i) := by
    intro i
    simp only [FormalODModule.Hom.toLawHom, IsLawHom.toHom_toPowerSeries]
    rfl
  have hnat : ∀ (m : CartierModule p Y.F), baseChange f₀ (CartierModule.map ρ.toLawHom m) =
      CartierModule.map (ρ.map f₀).toLawHom (baseChange f₀ m) :=
    fun m => baseChangeEq_map f₀ rfl rfl (φ := ρ.toLawHom) (ψ := (ρ.map f₀).toLawHom) hts m
  have hρb : ∀ i, CartierModule.map (ρ.map f₀).toLawHom (δb i) = (p : WittVector p κ) • γb i := by
    intro i; fin_cases i
    · show CartierModule.map (ρ.map f₀).toLawHom (baseChange f₀ (δ 0)) = (p : WittVector p κ) • baseChange f₀ (γ 0)
      rw [← hnat, hρ0, map_sub, baseChangeEq_smul_witt, map_natCast, baseChangeEq_verschiebungInt, baseChangeEq_smul_witt,
        hW0 _ _ hf₀η (pow_pos hp0 2), zero_smul, map_zero, sub_zero]
    · show CartierModule.map (ρ.map f₀).toLawHom (baseChange f₀ (δ 1)) = (p : WittVector p κ) • baseChange f₀ (γ 1)
      rw [← hnat, hρ1, map_sub, baseChangeEq_smul_witt, map_natCast, baseChangeEq_verschiebungInt, baseChangeEq_smul_witt,
        hW0 _ _ hf₀ξ (pow_pos hp0 2), zero_smul, map_zero, sub_zero]

  obtain ⟨ι, hι0, hι1⟩ := CerednikDrinfeld.FormalODModule.exists_hom_map_eq_of_endAct_varpiEnd_eq_verschiebungInt p
    (f₀.comp j) (Y.map f₀) (X.map f₀) δb hδb hδb0 hδb1 γb hγb hγb0 hγb1
  obtain ⟨ι', hι'0, hι'1⟩ := CerednikDrinfeld.FormalODModule.exists_hom_map_eq_of_endAct_varpiEnd_eq_verschiebungInt p
    (f₀.comp j) (X.map f₀) (Y.map f₀) γb hγb hγb0 hγb1 δb hδb hδb0 hδb1
  have hιι' : (ι'.comp ι).toLawHom = (FormalODModule.Hom.id (Y.map f₀)).toLawHom := by
    refine lawHom_eq_of_apply_basis (f₀.comp j) (Y.map f₀) δb hδb hδb0 hδb1 _ _ (fun i => ?_)
    have hc : (ι'.comp ι).toLawHom = ι'.toLawHom.comp ι.toLawHom := rfl
    have hid : (FormalODModule.Hom.id (Y.map f₀)).toLawHom = MvFormalGroup.Hom.id _ := rfl
    rw [hc, CartierModule.map_comp, hid, CartierModule.map_id]
    fin_cases i
    · show CartierModule.map ι'.toLawHom (CartierModule.map ι.toLawHom (δb 0)) = δb 0
      rw [hι0, hι'0]
    · show CartierModule.map ι'.toLawHom (CartierModule.map ι.toLawHom (δb 1)) = δb 1
      rw [hι1, hι'1]
  have hinv : ι'.toSeries.comp ι.toSeries = Series.id κ := congrArg MvFormalGroup.Hom.toPowerSeries hιι'

  have hfac : (ρ.map f₀).toLawHom = ((X.map f₀).actEnd (p : Zp2 p)).comp ι.toLawHom := by
    refine lawHom_eq_of_apply_basis (f₀.comp j) (Y.map f₀) δb hδb hδb0 hδb1 _ _ (fun i => ?_)
    rw [hρb, CartierModule.map_comp, ← CartierModule.endAct_apply ((X.map f₀).actEnd _), endAct_actEnd_natCast,
      natCast_smul_eq_nsmul']
    fin_cases i
    · show p • γb 0 = p • CartierModule.map ι.toLawHom (δb 0)
      rw [hι0]
    · show p • γb 1 = p • CartierModule.map ι.toLawHom (δb 1)
      rw [hι1]
  have hser : ρ.toSeries.map f₀ = ((X.map f₀).act (p : Zp2 p)).comp ι.toSeries := congrArg MvFormalGroup.Hom.toPowerSeries hfac

  have hι0c : ∀ i, MvPowerSeries.constantCoeff (ι.toSeries i) = 0 := ι.isODHom.1.1
  have hdegι : FormalODModule.HasKernelOfDegree ι.toSeries (p ^ 0) :=
    hasKernelOfDegree_one_of_comp_eq_id p ι'.toSeries ι.toSeries ι'.isODHom.1.1 hι0c hinv
  have hdegp : FormalODModule.HasKernelOfDegree ((X.map f₀).act (p : Zp2 p)) (p ^ 4) :=
    CerednikDrinfeld.FormalODModule.hasKernelOfDegree_map f₀ (X.act (p : Zp2 p)) (X.isLawHom_act _).1 hX4
  have hdeg : FormalODModule.HasKernelOfDegree (ρ.toSeries.map f₀) (p ^ 4) := by
    rw [hser, show p ^ 4 = p ^ 0 * p ^ 4 by rw [pow_zero, one_mul]]
    exact CerednikDrinfeld.FormalODModule.HasKernelOfDegree.comp hι0c ((X.map f₀).isLawHom_act _).1 hdegι hdegp
  have := hdeg.2.2 κ (RingHom.id κ)
  rwa [Series.map_ringHom_id] at this

end node
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_exists_isCartierQuadruple_map_line_eq_of_edge_isogeny_of_apply_xi_eq_zero_of_apply_eta_eq_zero.B29CMU"

end B30R1b
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_exists_isCartierQuadruple_map_line_eq_of_edge_isogeny_of_apply_xi_eq_zero_of_apply_eta_eq_zero.B29CMU P2MW.S_CerednikDrinfeld_FormalODModule_exists_isCartierQuadruple_map_line_eq_of_edge_isogeny_of_apply_xi_eq_zero_of_apply_eta_eq_zero.B30R1b"

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega MvFormalGroup MvFormalGroup.CartierModule

open scoped PadicInt Padic

namespace B39GN

open B30R1b B29CMU

variable (p : ℕ) [Fact p.Prime]

theorem isField_quot (k : Type) [Field k] [CharP k p] [PerfectRing k p] :
    IsField (WittVector p k ⧸ pIdeal p (WittVector p k)) := by
  obtain ⟨e⟩ := WittVector.nonempty_ringEquiv_quotient_pIdeal_of_perfectRing p k
  exact MulEquiv.isField (Field.toIsField k) e.symm.toMulEquiv

@[reducible] noncomputable def fieldQuot (k : Type) [Field k] [CharP k p] [PerfectRing k p] :
    Field (WittVector p k ⧸ pIdeal p (WittVector p k)) :=
  (isField_quot p k).toField

scoped instance charP_quot (k : Type) [Field k] [CharP k p] [PerfectRing k p] :
    CharP (WittVector p k ⧸ pIdeal p (WittVector p k)) p := by
  haveI : Nontrivial (WittVector p k ⧸ pIdeal p (WittVector p k)) := (isField_quot p k).nontrivial
  rw [CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)]
  exact (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.subset_span (Set.mem_singleton _))

scoped instance isNoetherianRing_edgeRingCharP (k : Type) [CommRing k] [IsNoetherianRing k] :
    IsNoetherianRing (EdgeFamily.edgeRingCharP p k) :=
  IsLocalization.isNoetherianRing (Submonoid.powers (FormalOmega.edgeQuot.discr k (0 : k) p)) _
    (show IsNoetherianRing (MvPolynomial (Fin 2) k ⧸ Ideal.span {FormalOmega.edgeRel k (0 : k)}) from inferInstance)

section rho1

variable {p}
variable {R : Type} [CommRing R] [CharP R p] {K : Type} [CommRing K] [CharP K p]

omit [CharP R p] [CharP K p] in

theorem baseChangeEq_retract {d : ℕ} {F : MvFormalGroup d K} [F.IsComm]
    (f₀ : R →+* K) (s : K →+* R) (hfs : f₀.comp s = RingHom.id K)
    (h : (F.map s).map f₀ = F) (x : CartierModule p F) :
    baseChangeEq f₀ h (baseChange s x) = x := by
  have h'' : F.map (f₀.comp s) = F := by rw [hfs, MvFormalGroup.map_ringHom_id']
  show baseChangeEq f₀ h (baseChangeEq s rfl x) = x
  rw [baseChangeEq_baseChangeEq s f₀ rfl h h'']
  have key : ∀ (g : K →+* K) (hg : g = RingHom.id K) (h₁ : F.map g = F), baseChangeEq g h₁ x = x := by
    intro g hg h₁; subst hg; exact baseChangeEq_id h₁ x
  exact key _ hfs h''

theorem map_node_eq_act (j : Zp2 p →+* R) (ξ η : R) (hξη : ξ * η = 0)
    (f₀ : R →+* K) (s : K →+* R) (hfs : f₀.comp s = RingHom.id K)
    (hf₀ξ : f₀ ξ = 0) (hf₀η : f₀ η = 0)
    (X : FormalODModule p R) (γ : Fin 2 → CartierModule p X.F) (hγ : X.IsHomogeneousVBasis j γ)
    (ha : X.HasStructureConstants γ (EdgeFamily.edgeConstants p ξ η))
    (ρ₁ : FormalODModule.Hom ((X.map f₀).map s) X)
    (hρ₁0 : CartierModule.map ρ₁.toLawHom (baseChange s (baseChange f₀ (γ 0))) =
      (p : WittVector p R) • γ 0 - verschiebungInt (WittVector.teichmuller p (η ^ p ^ 2) • γ 1))
    (hρ₁1 : CartierModule.map ρ₁.toLawHom (baseChange s (baseChange f₀ (γ 1))) =
      (p : WittVector p R) • γ 1 - verschiebungInt (WittVector.teichmuller p (ξ ^ p ^ 2) • γ 0)) :
    ρ₁.toSeries.map f₀ = (X.map f₀).act (p : Zp2 p) := by
  have hW0 : ∀ (x : R) (n : ℕ), f₀ x = 0 → 0 < n → WittVector.map f₀ (WittVector.teichmuller p (x ^ n)) = 0 := by
    intro x n hx hn
    rw [WittVector.map_teichmuller, map_pow, hx, zero_pow hn.ne', WittVector.teichmuller_zero]
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨hγ0, hγ1⟩ :=
    CerednikDrinfeld.FormalODModule.endAct_varpiEnd_eq_teichmuller_sub_smul_add_verschiebungInt_of_hasStructureConstants_edgeConstants
      p j ξ η hξη X γ hγ ha
  have hγb := hγ.map f₀
  have hγb0 : endAct (X.map f₀).varpiEnd (baseChange f₀ (γ 0)) = verschiebungInt (baseChange f₀ (γ 0)) := by
    rw [← FormalODModule.baseChange_endAct_varpiEnd, hγ0, map_add, baseChangeEq_smul_witt, baseChangeEq_verschiebungInt, map_sub,
      hW0 _ _ hf₀η hp0, show WittVector.teichmuller p η = WittVector.teichmuller p (η ^ 1) by rw [pow_one],
      hW0 _ _ hf₀η one_pos, sub_self, zero_smul, zero_add]
  have hγb1 : endAct (X.map f₀).varpiEnd (baseChange f₀ (γ 1)) = verschiebungInt (baseChange f₀ (γ 1)) := by
    rw [← FormalODModule.baseChange_endAct_varpiEnd, hγ1, map_add, baseChangeEq_smul_witt, baseChangeEq_verschiebungInt, map_sub,
      hW0 _ _ hf₀ξ hp0, show WittVector.teichmuller p ξ = WittVector.teichmuller p (ξ ^ 1) by rw [pow_one],
      hW0 _ _ hf₀ξ one_pos, sub_self, zero_smul, zero_add]

  have hYF : (((X.map f₀).map s).map f₀).F = (X.map f₀).F := by
    show ((X.F.map f₀).map s).map f₀ = X.F.map f₀
    rw [MvFormalGroup.map_map_ringHom, hfs, MvFormalGroup.map_ringHom_id']
  have hlaw : IsLawHom (X.map f₀).F (X.map f₀).F (ρ₁.toSeries.map f₀) := by
    have h := (ρ₁.isODHom.map f₀).1
    rw [hYF] at h
    exact h
  have hts : ∀ i, hlaw.toHom.toPowerSeries i = MvPowerSeries.map f₀ (ρ₁.toLawHom.toPowerSeries i) := by
    intro i
    simp only [FormalODModule.Hom.toLawHom, IsLawHom.toHom_toPowerSeries]
    rfl
  have hnat : ∀ x : CartierModule p ((X.map f₀).map s).F,
      baseChange f₀ (CartierModule.map ρ₁.toLawHom x) = CartierModule.map hlaw.toHom (baseChangeEq f₀ hYF x) :=
    fun x => baseChangeEq_map f₀ hYF rfl (φ := ρ₁.toLawHom) (ψ := hlaw.toHom) hts x
  have hψ : ∀ i, CartierModule.map hlaw.toHom (baseChange f₀ (γ i)) = (p : WittVector p K) • baseChange f₀ (γ i) := by
    intro i
    have r : baseChangeEq f₀ hYF (baseChange s (baseChange f₀ (γ i))) = baseChange f₀ (γ i) :=
      baseChangeEq_retract f₀ s hfs hYF _
    have e : CartierModule.map hlaw.toHom (baseChange f₀ (γ i)) =
        baseChange f₀ (CartierModule.map ρ₁.toLawHom (baseChange s (baseChange f₀ (γ i)))) := by
      rw [hnat, r]
    rw [e]
    fin_cases i
    · show baseChange f₀ (CartierModule.map ρ₁.toLawHom (baseChange s (baseChange f₀ (γ 0)))) =
        (p : WittVector p K) • baseChange f₀ (γ 0)
      rw [hρ₁0, map_sub, baseChangeEq_smul_witt, map_natCast, baseChangeEq_verschiebungInt, baseChangeEq_smul_witt,
        hW0 _ _ hf₀η (pow_pos hp0 2), zero_smul, map_zero, sub_zero]
    · show baseChange f₀ (CartierModule.map ρ₁.toLawHom (baseChange s (baseChange f₀ (γ 1)))) =
        (p : WittVector p K) • baseChange f₀ (γ 1)
      rw [hρ₁1, map_sub, baseChangeEq_smul_witt, map_natCast, baseChangeEq_verschiebungInt, baseChangeEq_smul_witt,
        hW0 _ _ hf₀ξ (pow_pos hp0 2), zero_smul, map_zero, sub_zero]
  have hfac : hlaw.toHom = (X.map f₀).actEnd (p : Zp2 p) := by
    refine lawHom_eq_of_apply_basis (f₀.comp j) (X.map f₀) (fun i => baseChange f₀ (γ i)) hγb hγb0 hγb1 _ _ (fun i => ?_)
    show CartierModule.map hlaw.toHom (baseChange f₀ (γ i)) =
      CartierModule.map ((X.map f₀).actEnd (p : Zp2 p)) (baseChange f₀ (γ i))
    rw [hψ, ← CartierModule.endAct_apply ((X.map f₀).actEnd _), endAct_actEnd_natCast, natCast_smul_eq_nsmul']
    rfl
  have := congrArg MvFormalGroup.Hom.toPowerSeries hfac
  rw [FormalODModule.actEnd_toPowerSeries] at this
  rw [← this]
  exact (IsLawHom.toHom_toPowerSeries hlaw).symm

end rho1
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_exists_isCartierQuadruple_map_line_eq_of_edge_isogeny_of_apply_xi_eq_zero_of_apply_eta_eq_zero.B29CMU P2MW.S_CerednikDrinfeld_FormalODModule_exists_isCartierQuadruple_map_line_eq_of_edge_isogeny_of_apply_xi_eq_zero_of_apply_eta_eq_zero.B30R1b"

section assemble

variable {p}
variable {O : Type} [CommRing O] {Φ : FormalODModule p (O ⧸ pIdeal p O)}
variable {R : Type} [CommRing R]

theorem map_node_eq (f₀ : R →+* O ⧸ pIdeal p O) (s : O ⧸ pIdeal p O →+* R) (hfs : f₀.comp s = RingHom.id _)
    (X : FormalODModule p R) (n : ℕ) (σ : Series R) (ρ₀ : Series (O ⧸ pIdeal p O))
    (h0 : ∀ i, MvPowerSeries.constantCoeff (ρ₀ i) = 0)
    (hσ : σ.map f₀ = (X.map f₀).act (p : Zp2 p)) :
    (Rigidified.mk (Φ := Φ) X n ((σ.map (Ideal.Quotient.mk (pIdeal p R))).comp
        (ρ₀.map ((Ideal.Quotient.mk (pIdeal p R)).comp s)))).map f₀ =
      Rigidified.mk (Φ := Φ) (X.map f₀) n
        ((((X.map f₀).map (Ideal.Quotient.mk (pIdeal p (O ⧸ pIdeal p O)))).act (p : Zp2 p)).comp
          (ρ₀.map (Ideal.Quotient.mk (pIdeal p (O ⧸ pIdeal p O))))) := by
  refine Rigidified.ext' rfl rfl ?_
  show ((σ.map (Ideal.Quotient.mk (pIdeal p R))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p R)).comp s))).map (reduceMap f₀) = _
  have h0' : ∀ i, MvPowerSeries.constantCoeff ((ρ₀.map ((Ideal.Quotient.mk (pIdeal p R)).comp s)) i) = 0 := by
    intro i
    show MvPowerSeries.constantCoeff (MvPowerSeries.map _ (ρ₀ i)) = 0
    rw [MvPowerSeries.constantCoeff_map, h0 i, map_zero]
  have hred1 : (reduceMap (p := p) f₀).comp (Ideal.Quotient.mk (pIdeal p R)) =
      (Ideal.Quotient.mk (pIdeal p (O ⧸ pIdeal p O))).comp f₀ := RingHom.ext fun _ => rfl
  have hred2 : (reduceMap (p := p) f₀).comp ((Ideal.Quotient.mk (pIdeal p R)).comp s) =
      Ideal.Quotient.mk (pIdeal p (O ⧸ pIdeal p O)) := by
    refine RingHom.ext fun x => ?_
    show Ideal.Quotient.mk (pIdeal p (O ⧸ pIdeal p O)) (f₀ (s x)) = Ideal.Quotient.mk (pIdeal p (O ⧸ pIdeal p O)) x
    rw [← RingHom.comp_apply f₀ s, hfs, RingHom.id_apply]
  rw [Series.map_comp _ _ _ h0', Series.map_map, Series.map_map, hred1, hred2, ← Series.map_map f₀, hσ]
  rfl

theorem isIsomorphic_shift {B : Type} [CommRing B] (X : FormalODModule p B) (n : ℕ) (ρ : Series (B ⧸ pIdeal p B))
    (h0 : ∀ i, MvPowerSeries.constantCoeff (ρ i) = 0) :
    (Rigidified.mk (Φ := Φ) X n ρ).IsIsomorphic
      (Rigidified.mk (Φ := Φ) X (n + 1) ((((X.map (Ideal.Quotient.mk (pIdeal p B)))).act (p : Zp2 p)).comp ρ)) := by
  refine ⟨Series.id B, Series.id B, 0, FormalODModule.IsODHom.id X, FormalODModule.IsODHom.id X,
    Series.comp_id _, Series.comp_id _, ?_⟩
  have hc : ∀ i, MvPowerSeries.constantCoeff (((X.map (Ideal.Quotient.mk (pIdeal p B))).act (p : Zp2 p)) i) = 0 :=
    ((X.map (Ideal.Quotient.mk (pIdeal p B))).isLawHom_act _).1
  show ((X.map (Ideal.Quotient.mk (pIdeal p B))).act ((p : Zp2 p) ^ (0 + (n + 1)))).comp
      (((Series.id B).map (Ideal.Quotient.mk (pIdeal p B))).comp ρ) =
    ((X.map (Ideal.Quotient.mk (pIdeal p B))).act ((p : Zp2 p) ^ (0 + n))).comp
      ((((X.map (Ideal.Quotient.mk (pIdeal p B)))).act (p : Zp2 p)).comp ρ)
  rw [Series.map_id, Series.id_comp _ h0, zero_add, zero_add, pow_succ, (X.map (Ideal.Quotient.mk (pIdeal p B))).act_mul,
    Series.comp_assoc _ _ _ hc h0]

theorem isAdmissible_node [IsNoetherianRing (O ⧸ pIdeal p O)] (ι : Zp2 p →+* O)
    (X0 : FormalODModule p (O ⧸ pIdeal p O))
    (hs : X0.IsSpecial (structureMap ι (Ideal.Quotient.mk (pIdeal p O)))) (h4 : X0.HasHeight 4)
    (m : ℕ) (ρ₀ : Series (O ⧸ pIdeal p O)) (hρ₀ : FormalODModule.IsIsogenyOfHeight Φ X0 ρ₀ (4 * m)) :
    (Rigidified.mk (Φ := Φ) X0 m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (O ⧸ pIdeal p O))))).IsAdmissible ι
      (Ideal.Quotient.mk (pIdeal p O)) := by
  refine ⟨hs, h4, ?_⟩
  show FormalODModule.IsIsogenyOfHeight (Φ.map (residueMap (Ideal.Quotient.mk (pIdeal p O))))
    (X0.map (Ideal.Quotient.mk (pIdeal p (O ⧸ pIdeal p O)))) (ρ₀.map (Ideal.Quotient.mk (pIdeal p (O ⧸ pIdeal p O)))) (4 * m)
  have hres : residueMap (p := p) (Ideal.Quotient.mk (pIdeal p O)) = Ideal.Quotient.mk (pIdeal p (O ⧸ pIdeal p O)) := by
    apply Ideal.Quotient.ringHom_ext; ext x; rfl
  rw [hres]
  exact ⟨hρ₀.1.map _, CerednikDrinfeld.FormalODModule.hasKernelOfDegree_map _ ρ₀ hρ₀.1.1.1 hρ₀.2⟩

theorem isAdmissible_edge [IsNoetherianRing (O ⧸ pIdeal p O)] [IsNoetherianRing R] (ι : Zp2 p →+* O)
    (f₀ : R →+* O ⧸ pIdeal p O) (s : O ⧸ pIdeal p O →+* R)
    (X : FormalODModule p R) (hXs : X.IsSpecial (structureMap ι (s.comp (Ideal.Quotient.mk (pIdeal p O)))))
    (hX4 : X.HasHeight 4) (m : ℕ) (ρ₀ : Series (O ⧸ pIdeal p O))
    (hρ₀ : FormalODModule.IsIsogenyOfHeight Φ (X.map f₀) ρ₀ (4 * m))
    (ρ₁ : FormalODModule.Hom ((X.map f₀).map s) X)
    (hρ₁h : FormalODModule.IsIsogenyOfHeight ((X.map f₀).map s) X ρ₁.toSeries 4) :
    (Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p R))).comp
        (ρ₀.map ((Ideal.Quotient.mk (pIdeal p R)).comp s)))).IsAdmissible ι (s.comp (Ideal.Quotient.mk (pIdeal p O))) := by
  refine ⟨hXs, hX4, ?_⟩
  show FormalODModule.IsIsogenyOfHeight (Φ.map (residueMap (s.comp (Ideal.Quotient.mk (pIdeal p O)))))
    (X.map (Ideal.Quotient.mk (pIdeal p R)))
    ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p R))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p R)).comp s))) (4 * (m + 1))
  have hres : residueMap (p := p) (s.comp (Ideal.Quotient.mk (pIdeal p O))) = (Ideal.Quotient.mk (pIdeal p R)).comp s := by
    apply Ideal.Quotient.ringHom_ext; ext x; rfl
  rw [hres]
  have h1 : FormalODModule.IsODHom ((X.map f₀).map ((Ideal.Quotient.mk (pIdeal p R)).comp s)) (X.map (Ideal.Quotient.mk (pIdeal p R)))
      (ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p R))) := by
    have h := ρ₁.isODHom.map (Ideal.Quotient.mk (pIdeal p R))
    rw [FormalODModule.map_map s (Ideal.Quotient.mk (pIdeal p R)) (X.map f₀)] at h
    exact h
  refine ⟨h1.comp (hρ₀.1.map _), ?_⟩
  have d0 : FormalODModule.HasKernelOfDegree (ρ₀.map ((Ideal.Quotient.mk (pIdeal p R)).comp s)) (p ^ (4 * m)) :=
    CerednikDrinfeld.FormalODModule.hasKernelOfDegree_map _ ρ₀ hρ₀.1.1.1 hρ₀.2
  have d1 : FormalODModule.HasKernelOfDegree (ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p R))) (p ^ 4) :=
    CerednikDrinfeld.FormalODModule.hasKernelOfDegree_map _ ρ₁.toSeries ρ₁.isODHom.1.1 hρ₁h.2
  rw [show p ^ (4 * (m + 1)) = p ^ (4 * m) * p ^ 4 by ring]
  exact CerednikDrinfeld.FormalODModule.HasKernelOfDegree.comp (hρ₀.1.map _).1.1 h1.1.1 d0 d1

end assemble
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_exists_isCartierQuadruple_map_line_eq_of_edge_isogeny_of_apply_xi_eq_zero_of_apply_eta_eq_zero.B29CMU P2MW.S_CerednikDrinfeld_FormalODModule_exists_isCartierQuadruple_map_line_eq_of_edge_isogeny_of_apply_xi_eq_zero_of_apply_eta_eq_zero.B30R1b"

end B39GN
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_exists_isCartierQuadruple_map_line_eq_of_edge_isogeny_of_apply_xi_eq_zero_of_apply_eta_eq_zero.B29CMU P2MW.S_CerednikDrinfeld_FormalODModule_exists_isCartierQuadruple_map_line_eq_of_edge_isogeny_of_apply_xi_eq_zero_of_apply_eta_eq_zero.B30R1b P2MW.S_CerednikDrinfeld_FormalODModule_exists_isCartierQuadruple_map_line_eq_of_edge_isogeny_of_apply_xi_eq_zero_of_apply_eta_eq_zero.B39GN"

theorem solution
(p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
(ι : Zp2 p →+* WittVector p k)
(Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
(hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι))
(hΦ4 : Φ.HasHeight 4)
(h0Φ : Φ.lieZero ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) ≤ LinearMap.ker Φ.lieVarpi)
(hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0) (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
(rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
(hrΦ : ∀ (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
  (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L),
  Set.BijOn rΦ Set.univ ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung 0 : Set _))
(g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p])
(hg : (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) = Matrix.diagonal ![algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]), 1])
(X : FormalODModule p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (γ : Fin 2 → CartierModule p X.F)
(hγ : X.IsHomogeneousVBasis (structureMap ι ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) γ)
(hγa : X.HasStructureConstants γ (EdgeFamily.edgeRingConstants p (WittVector p k ⧸ pIdeal p (WittVector p k))))
(hXs : X.IsSpecial (structureMap ι ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))))) (hX4 : X.HasHeight 4)

(f₀ : (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))) →+* (WittVector p k ⧸ pIdeal p (WittVector p k)))
(hf₀ : f₀.comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) = RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))
(hf₀ξ : f₀ (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))) = 0) (hf₀η : f₀ (EdgeFamily.edgeRingCharP.η p (WittVector p k ⧸ pIdeal p (WittVector p k))) = 0)
(m : ℕ) (ρ₀ : Series (WittVector p k ⧸ pIdeal p (WittVector p k)))
(hρ₀ : FormalODModule.IsIsogenyOfHeight Φ (X.map f₀) ρ₀ (4 * m))
(hOD₀ : FormalODModule.IsODHom (Rigidified.Φbar (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))))))) (Rigidified.Xbar (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))))))) (Rigidified.ρ (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))))))))
(hcb : Rigidified.IsGradedSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k))))
(hcΦg : Rigidified.IsGradedPhiS (Φ := Φ) ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k))))
(a : ℕ)
(hN : ∀ i : Fin 2,
    p ^ a • (Rigidified.rigidNum ι hcΦ rΦ (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) hOD₀ (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k))) hcb hcΦg) (Pi.single i 1) =
      p ^ (a + m) • (![((Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb).nMk ((baseChange (reduceMap (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange f₀ (γ 0)))), 0),
          ((Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb).nVarpi (((Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb).nMk ((baseChange (reduceMap (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange f₀ (γ 1)))), 0))] i))
(ρ₁ : FormalODModule.Hom ((X.map f₀).map (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))) X)
(hρ₁0 : CartierModule.map ρ₁.toLawHom (baseChange (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange f₀ (γ 0))) =
    (p : WittVector p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) • γ 0 -
      verschiebungInt (WittVector.teichmuller p ((EdgeFamily.edgeRingCharP.η p (WittVector p k ⧸ pIdeal p (WittVector p k))) ^ p ^ 2) • γ 1))
(hρ₁1 : CartierModule.map ρ₁.toLawHom (baseChange (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange f₀ (γ 1))) =
    (p : WittVector p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) • γ 1 -
      verschiebungInt (WittVector.teichmuller p ((EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))) ^ p ^ 2) • γ 0))
(hρ₁h : FormalODModule.IsIsogenyOfHeight ((X.map f₀).map (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))) X ρ₁.toSeries 4)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra ℤ_[p] Ω] (y : (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))) →+* Ω)
    (hyξ : y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))) = 0) (hyη : y (EdgeFamily.edgeRingCharP.η p (WittVector p k ⧸ pIdeal p (WittVector p k))) = 0)
    :
      ∃ (Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) Ω) (d : DeligneDatum (K := ℚ_[p]) (p : ℤ_[p]) Ω),
        ((Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y).IsCartierQuadruple ι hcΦ rΦ (y.comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) Q ∧
        Q.IsQuadrupleOf d ∧
        d.line (stdFullLattice ℚ_[p]) =
            Submodule.span Ω {(y (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k)))) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 0 + (1 : Ω) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1} ∧
          d.line (FullLattice.act g (stdFullLattice ℚ_[p])) =
            (Submodule.span Ω {(1 : Ω) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 0 + (y (EdgeFamily.edgeRingCharP.η p (WittVector p k ⧸ pIdeal p (WittVector p k)))) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1}).map
              (actBaseChange Ω g (stdFullLattice ℚ_[p])).toLinearMap := by
  letI _instF : Field (WittVector p k ⧸ pIdeal p (WittVector p k)) := B39GN.fieldQuot p k
  haveI _instN : Nontrivial (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))) := f₀.domain_nontrivial
  haveI _instC : CharP (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))) p := by
    rw [CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime), ← map_natCast (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))), CharP.cast_eq_zero, map_zero]
  have hρ₀c : ∀ i, MvPowerSeries.constantCoeff (ρ₀ i) = 0 := hρ₀.1.1.1
  have hρb0c : ∀ i, MvPowerSeries.constantCoeff ((ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))))) i) = 0 := fun i => by
    show MvPowerSeries.constantCoeff (MvPowerSeries.map _ (ρ₀ i)) = 0
    rw [MvPowerSeries.constantCoeff_map, hρ₀c i, map_zero]

  have hσ : ρ₁.toSeries.map f₀ = (X.map f₀).act (p : Zp2 p) :=
    B39GN.map_node_eq_act (structureMap ι ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))))
      (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))) (EdgeFamily.edgeRingCharP.η p (WittVector p k ⧸ pIdeal p (WittVector p k))) (EdgeFamily.edgeRingCharP.ξ_mul_η p (WittVector p k ⧸ pIdeal p (WittVector p k)))
      f₀ (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) hf₀ hf₀ξ hf₀η X γ hγ hγa ρ₁ hρ₁0 hρ₁1

  have ht0 : (Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map f₀ = (Rigidified.mk (Φ := Φ) (X.map f₀) (m + 1) ((((X.map f₀).map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))))).act (p : Zp2 p)).comp (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))))))) :=
    B39GN.map_node_eq f₀ (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) hf₀ X (m + 1) ρ₁.toSeries ρ₀ hρ₀c hσ

  have hy : y = (y.comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp f₀ :=
    CerednikDrinfeld.EdgeFamily.edgeRingCharP.eq_comp_of_apply_xi_eq_zero_of_apply_eta_eq_zero p (WittVector p k ⧸ pIdeal p (WittVector p k)) f₀ hf₀ hf₀ξ hf₀η y hyξ hyη
  have ht : (Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map y = (Rigidified.mk (Φ := Φ) (X.map f₀) (m + 1) ((((X.map f₀).map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))))).act (p : Zp2 p)).comp (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))))))).map (y.comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))) := by
    have e : (Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).map ((y.comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp f₀) = (Rigidified.mk (Φ := Φ) (X.map f₀) (m + 1) ((((X.map f₀).map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))))).act (p : Zp2 p)).comp (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))))))).map (y.comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))) := by
      rw [Rigidified.map_comp, ht0]
    rw [← hy] at e
    exact e

  obtain ⟨Q, d, hQ, hd, hl0, hl1⟩ :=
    CerednikDrinfeld.FormalODModule.forall_isCartierQuadruple_map_node_line_eq_of_rigidNum_single_eq p k ι Φ hΦ hΦ4 h0Φ hcΦ rΦ hrΦ
      g hg X γ hγ hγa hXs hX4 f₀ hf₀ hf₀ξ hf₀η m ρ₀ hρ₀ hOD₀ hcb hcΦg a hN Ω (y.comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))
  refine ⟨Q, d, ?_, hd, ?_, ?_⟩
  · rw [ht]
    have hstr : f₀.comp (structureMap ι ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) = structureMap ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) :=
      RingHom.ext fun x => by
        show f₀ ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) ((Ideal.Quotient.mk (pIdeal p (WittVector p k))) (ι x))) = (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (ι x)
        rw [← RingHom.comp_apply f₀ (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))), hf₀, RingHom.id_apply]
    have hXs0 : (X.map f₀).IsSpecial (structureMap ι (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) := by
      have h := CerednikDrinfeld.FormalODModule.IsSpecial.map _ f₀ X hXs
      rw [hstr] at h
      exact h
    have hX40 : (X.map f₀).HasHeight 4 :=
      CerednikDrinfeld.FormalODModule.hasKernelOfDegree_map f₀ (X.act (p : Zp2 p)) (X.isLawHom_act _).1 hX4
    have hadm0K : (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).IsAdmissible ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) :=
      B39GN.isAdmissible_node ι (X.map f₀) hXs0 hX40 m ρ₀ hρ₀
    have hadm1K : (Rigidified.mk (Φ := Φ) (X.map f₀) (m + 1) ((((X.map f₀).map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))))).act (p : Zp2 p)).comp (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))))))).IsAdmissible ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) := by
      have h := Rigidified.IsAdmissible.map_ringHom ι ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) f₀ (Rigidified.mk (Φ := Φ) X (m + 1) ((ρ₁.toSeries.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))))))
        (B39GN.isAdmissible_edge ι f₀ (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) X hXs hX4 m ρ₀ hρ₀ ρ₁ hρ₁h)
      rw [ht0, ← RingHom.comp_assoc, hf₀, RingHom.id_comp] at h
      exact h
    have hadm0 := Rigidified.IsAdmissible.map_ringHom ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (y.comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))) (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) hadm0K
    have hadm1 := Rigidified.IsAdmissible.map_ringHom ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (y.comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))) (Rigidified.mk (Φ := Φ) (X.map f₀) (m + 1) ((((X.map f₀).map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))))).act (p : Zp2 p)).comp (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))))))) hadm1K
    have hiso : ((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map (y.comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).IsIsomorphic ((Rigidified.mk (Φ := Φ) (X.map f₀) (m + 1) ((((X.map f₀).map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))))).act (p : Zp2 p)).comp (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))))))).map (y.comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) :=
      Rigidified.IsIsomorphic.map_ringHom (y.comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))) (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (Rigidified.mk (Φ := Φ) (X.map f₀) (m + 1) ((((X.map f₀).map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))))).act (p : Zp2 p)).comp (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))))))) hρb0c
        (Series.constantCoeff_comp (((X.map f₀).map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))))).isLawHom_act _).1 hρb0c)
        (B39GN.isIsomorphic_shift (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))))) hρb0c)
    have hpΩ : IsNilpotent (p : Ω) :=
      ⟨1, by rw [pow_one, ← map_natCast (y.comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))) p, CharP.cast_eq_zero, map_zero]⟩
    exact Rigidified.IsCartierQuadruple.of_isIsomorphic p ι Φ hΦ hΦ4 hcΦ rΦ hrΦ ((y.comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) hpΩ _ _
      hadm0 hadm1 hiso Q hQ
  · rw [hyξ]; exact hl0
  · rw [hyη]; exact hl1

end S_CerednikDrinfeld_FormalODModule_exists_isCartierQuadruple_map_line_eq_of_edge_isogeny_of_apply_xi_eq_zero_of_apply_eta_eq_zero
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_isCartierQuadruple_map_line_eq_of_edge_isogeny_of_apply_xi_eq_zero_of_apply_eta_eq_zero (solution)
