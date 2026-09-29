-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_hom_map_eq_add_verschiebungInt_of_endAct_varpiEnd_eq_teichmuller
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/0a6fc174-058c-5441-ab4d-39d0da88a696

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
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Theorems.Thm_MvFormalGroup_CartierModule_existsUnique_addMonoidHom_apply_eq_of_frobenius_expansion
import Theorems.Thm_MvFormalGroup_CartierModule_exists_hom_forall_map_eq_of_algebra_padicInt
import Theorems.Thm_MvFormalGroup_CartierModule_eq_of_forall_map_eq_of_algebra_padicInt
import Theorems.Thm_MvFormalGroup_CartierModule_verschiebungInt_injective_of_algebra_padicInt
import Theorems.Thm_MvFormalGroup_CartierModule_existsUnique_eq_sum_verschiebungInt_iterate_homothety_add
import Theorems.Thm_MvFormalGroup_CartierModule_existsUnique_forall_eq_sum_range_verschiebungInt_iterate_add
import Theorems.Thm_WittVector_exists_eq_sum_iterate_verschiebung_teichmuller_add
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_hom_map_eq_add_verschiebungInt_of_endAct_varpiEnd_eq_teichmuller
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply"

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
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_exists_hom_map_eq_add_verschiebungInt_of_endAct_varpiEnd_eq_teichmuller.B29CMU"

namespace B29H2

open CerednikDrinfeld

variable (p : ℕ) [Fact p.Prime]

noncomputable def wd2 {R : Type} [CommRing R] (x : R) (n : ℕ) : R :=
  (WittVector.frobenius (WittVector.frobenius (WittVector.teichmuller p x)) - WittVector.teichmuller p x).coeff n

variable {p}

theorem wd2_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (x : R) (n : ℕ) :
    f (wd2 p x n) = wd2 p (f x) n := by
  have h1 : ∀ y : WittVector p R, WittVector.map f (WittVector.frobenius y) = WittVector.frobenius (WittVector.map f y) :=
    fun y => (WittVector.frobenius_isPoly p).map f y
  simp only [wd2]
  rw [← WittVector.map_coeff, map_sub, h1, h1, WittVector.map_teichmuller]

theorem wd2_zero {R : Type} [CommRing R] (n : ℕ) : wd2 p (0 : R) n = 0 := by
  simp [wd2, WittVector.teichmuller_zero]

theorem exists_wd2_eq_mul {R : Type} [CommRing R] (η : R) (n : ℕ) : ∃ e : R, wd2 p η n = η * e := by
  set P : Polynomial ℤ := wd2 p (Polynomial.X : Polynomial ℤ) n with hP
  have hmap : wd2 p η n = Polynomial.aeval η P := by
    have h := wd2_map (p := p) (Polynomial.aeval (R := ℤ) η).toRingHom (Polynomial.X : Polynomial ℤ) n
    have hX : (Polynomial.aeval (R := ℤ) η).toRingHom (Polynomial.X : Polynomial ℤ) = η := by
      show Polynomial.aeval η (Polynomial.X : Polynomial ℤ) = η
      exact Polynomial.aeval_X η
    rw [hX] at h
    rw [hP, ← h]
    rfl
  have h0 : P.coeff 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, hP, ← Polynomial.coe_evalRingHom, wd2_map (Polynomial.evalRingHom (0 : ℤ)) Polynomial.X n]
    simp [wd2_zero]
  obtain ⟨Q, hQ⟩ := Polynomial.X_dvd_iff.mpr h0
  refine ⟨Polynomial.aeval η Q, ?_⟩
  rw [hmap, hQ, map_mul, Polynomial.aeval_X]

end B29H2
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_exists_hom_map_eq_add_verschiebungInt_of_endAct_varpiEnd_eq_teichmuller.B29CMU"

namespace B29R1c

open MvFormalGroup MvFormalGroup.CartierModule

section generic2

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] {d : ℕ} {Φ : MvFormalGroup d R} [Φ.IsComm]

local notation "VV" => (verschiebungInt : CartierModule p Φ →+ CartierModule p Φ)
local notation "FF" => (MvFormalGroup.CartierModule.frobenius : CartierModule p Φ →+ CartierModule p Φ)
local notation "VW" => (WittVector.verschiebung : WittVector p R →+ WittVector p R)

theorem F_V [CharP R p] (t : CartierModule p Φ) : FF (VV t) = VV (FF t) := by
  rw [frobenius_verschiebungInt_eq_smul, verschiebungInt_apply_eq_verschiebung, verschiebung_frobenius_eq_smul]

theorem F_iterV [CharP R p] (K : ℕ) (t : CartierModule p Φ) : FF ((⇑VV)^[K] t) = (⇑VV)^[K] (FF t) := by
  induction K with
  | zero => rfl
  | succ K ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', F_V, ih]

theorem iterF_iterV [CharP R p] (n K : ℕ) (t : CartierModule p Φ) : (⇑FF)^[n] ((⇑VV)^[K] t) = (⇑VV)^[K] ((⇑FF)^[n] t) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, F_iterV]

theorem homothety_iterV (c : R) (K : ℕ) (t : CartierModule p Φ) :
    homothety c ((⇑VV)^[K] t) = (⇑VV)^[K] (homothety (c ^ p ^ K) t) := by
  induction K generalizing c with
  | zero => simp
  | succ K ih => rw [Function.iterate_succ_apply', homothety_verschiebungInt, ih, Function.iterate_succ_apply',
      ← pow_mul, ← pow_succ']

theorem iterF_homothety (e : R) (n : ℕ) (t : CartierModule p Φ) :
    (⇑FF)^[n] (homothety e t) = homothety (e ^ p ^ n) ((⇑FF)^[n] t) := by
  induction n generalizing e with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', ih, frobenius_homothety, Function.iterate_succ_apply', ← pow_mul,
      ← pow_succ]

theorem iterVW_smul (n : ℕ) (w : WittVector p R) (x : CartierModule p Φ) :
    ((⇑VW)^[n] w) • x = (⇑VV)^[n] (w • (⇑FF)^[n] x) := by
  induction n generalizing w x with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih, Function.iterate_succ_apply, ← verschiebungInt_smul_frobenius,
      Function.iterate_succ_apply']

theorem iterV_add (K : ℕ) (x y : CartierModule p Φ) : (⇑VV)^[K] (x + y) = (⇑VV)^[K] x + (⇑VV)^[K] y := by
  induction K with
  | zero => rfl
  | succ K ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_add]

theorem iterV_zero (K : ℕ) : (⇑VV)^[K] (0 : CartierModule p Φ) = 0 := Function.iterate_fixed (map_zero _) K

end generic2
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_exists_hom_map_eq_add_verschiebungInt_of_endAct_varpiEnd_eq_teichmuller.B29CMU"

section branch

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] {d : ℕ} {Φ : MvFormalGroup d R} [Φ.IsComm]

local notation "VV" => (verschiebungInt : CartierModule p Φ →+ CartierModule p Φ)
local notation "FF" => (MvFormalGroup.CartierModule.frobenius : CartierModule p Φ →+ CartierModule p Φ)

noncomputable def iterF (n : ℕ) : CartierModule p Φ →+ CartierModule p Φ where
  toFun := (⇑FF)^[n]
  map_zero' := Function.iterate_fixed (map_zero _) n
  map_add' a b := by
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_add]

@[scoped simp] theorem iterF_apply (n : ℕ) (f : CartierModule p Φ) : iterF (p := p) (Φ := Φ) n f = (⇑FF)^[n] f := rfl

noncomputable def iterV (k : ℕ) : CartierModule p Φ →+ CartierModule p Φ where
  toFun := (⇑VV)^[k]
  map_zero' := Function.iterate_fixed (map_zero _) k
  map_add' a b := iterV_add k a b

@[scoped simp] theorem iterV_apply (k : ℕ) (f : CartierModule p Φ) : iterV (p := p) (Φ := Φ) k f = (⇑VV)^[k] f := rfl

noncomputable def T (x : R) (g : CartierModule p Φ) : AddSubgroup (CartierModule p Φ) :=
  AddSubgroup.closure (Set.range fun kr : ℕ × R => (⇑VV)^[kr.1] (homothety (x * kr.2) g))

theorem gen_mem_T (x : R) (g : CartierModule p Φ) (k : ℕ) (r : R) :
    (⇑VV)^[k] (homothety (x * r) g) ∈ T (p := p) x g :=
  AddSubgroup.subset_closure ⟨(k, r), rfl⟩

theorem V_mem_T (x : R) (g : CartierModule p Φ) {J : CartierModule p Φ} (hJ : J ∈ T (p := p) x g) :
    verschiebungInt J ∈ T (p := p) x g := by
  induction hJ using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨⟨k, r⟩, rfl⟩ := hy
    have := gen_mem_T (p := p) x g (k + 1) r
    rwa [Function.iterate_succ_apply'] at this
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | neg a _ ha => rw [map_neg]; exact neg_mem ha

theorem iterV_mem_T (x : R) (g : CartierModule p Φ) (k : ℕ) {J : CartierModule p Φ} (hJ : J ∈ T (p := p) x g) :
    (⇑VV)^[k] J ∈ T (p := p) x g := by
  induction k with
  | zero => exact hJ
  | succ k ih => rw [Function.iterate_succ_apply']; exact V_mem_T x g ih

theorem homothety_iterF_eq_zero_of_mem_T [CharP R p] (x : R) (g : CartierModule p Φ) (c : R) (hc : c * x = 0) (n : ℕ)
    {J : CartierModule p Φ} (hJ : J ∈ T (p := p) x g) : homothety c ((⇑FF)^[n] J) = 0 := by
  have key : T (p := p) x g ≤ ((homothety c : CartierModule p Φ →+ _).comp (iterF (p := p) (Φ := Φ) n)).ker := by
    unfold T
    rw [AddSubgroup.closure_le]
    rintro _ ⟨⟨k, r⟩, rfl⟩
    rw [SetLike.mem_coe, AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, iterF_apply, iterF_iterV, homothety_iterV,
      iterF_homothety, ← homothety_mul]
    have : c ^ p ^ k * (x * r) ^ p ^ n = 0 := by
      have hk : 1 ≤ p ^ k := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
      have hn : 1 ≤ p ^ n := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
      obtain ⟨a, ha⟩ := Nat.exists_eq_add_of_le hk
      obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le hn
      rw [ha, hb, pow_add, pow_one, pow_add, pow_one]
      calc c * c ^ a * (x * r * (x * r) ^ b) = (c * x) * (c ^ a * r * (x * r) ^ b) := by ring
        _ = 0 := by rw [hc, zero_mul]
    rw [this, homothety_zero_left, iterV_zero]
  exact (AddMonoidHom.mem_ker).1 (key hJ)

end branch
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_exists_hom_map_eq_add_verschiebungInt_of_endAct_varpiEnd_eq_teichmuller.B29CMU"

end B29R1c
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_exists_hom_map_eq_add_verschiebungInt_of_endAct_varpiEnd_eq_teichmuller.B29CMU P2MW.S_CerednikDrinfeld_FormalODModule_exists_hom_map_eq_add_verschiebungInt_of_endAct_varpiEnd_eq_teichmuller.B29R1c"

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
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_exists_hom_map_eq_add_verschiebungInt_of_endAct_varpiEnd_eq_teichmuller.B29CMU P2MW.S_CerednikDrinfeld_FormalODModule_exists_hom_map_eq_add_verschiebungInt_of_endAct_varpiEnd_eq_teichmuller.B29R1c"

end B29R1
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_exists_hom_map_eq_add_verschiebungInt_of_endAct_varpiEnd_eq_teichmuller.B29CMU P2MW.S_CerednikDrinfeld_FormalODModule_exists_hom_map_eq_add_verschiebungInt_of_endAct_varpiEnd_eq_teichmuller.B29R1c"

namespace B29H2

open CerednikDrinfeld MvFormalGroup MvFormalGroup.CartierModule B29R1c

section exact

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [CharP R p] {d : ℕ} {Φ : MvFormalGroup d R} [Φ.IsComm]

local notation "VV" => (verschiebungInt : CartierModule p Φ →+ CartierModule p Φ)
local notation "FF" => (MvFormalGroup.CartierModule.frobenius : CartierModule p Φ →+ CartierModule p Φ)

omit [CharP R p] in
theorem iterF_smul (n : ℕ) (w : WittVector p R) (x : CartierModule p Φ) :
    (⇑FF)^[n] (w • x) = ((⇑(WittVector.frobenius (p := p) (R := R)))^[n] w) • (⇑FF)^[n] x := by
  induction n generalizing w x with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, frobenius_smul, ih, Function.iterate_succ_apply, Function.iterate_succ_apply]

theorem teichmuller_smul_iterF (x0 x1 : CartierModule p Φ) (W' : WittVector p R)
    (hF1 : FF x1 = W' • x0 + VV x1) (n : ℕ) :
    ∀ c : R, (∀ a b : ℕ, WittVector.teichmuller p (c ^ p ^ a) *
        ((⇑(WittVector.frobenius (p := p) (R := R)))^[b] W') = 0) →
      WittVector.teichmuller p c • (⇑FF)^[n] x1 = (⇑VV)^[n] (WittVector.teichmuller p (c ^ p ^ n) • x1) := by
  induction n with
  | zero => intro c _; simp
  | succ n ih =>
    intro c hc
    have hcp : ∀ a b : ℕ, WittVector.teichmuller p ((c ^ p) ^ p ^ a) *
        ((⇑(WittVector.frobenius (p := p) (R := R)))^[b] W') = 0 := by
      intro a b; rw [← pow_mul, ← pow_succ']; exact hc (a + 1) b
    have h0 := hc 0 n
    rw [pow_zero, pow_one] at h0
    have hadd : ∀ a b : CartierModule p Φ, (⇑FF)^[n] (a + b) = (⇑FF)^[n] a + (⇑FF)^[n] b :=
      fun a b => (iterF (p := p) (Φ := Φ) n).map_add a b
    rw [Function.iterate_succ_apply, hF1, hadd, iterF_smul,
      smul_add, ← mul_smul, h0, zero_smul, zero_add, show (⇑FF)^[n] (VV x1) = VV ((⇑FF)^[n] x1) from iterF_iterV n 1 x1,
      smul_verschiebungInt,
      WittVector.frobenius_teichmuller_eq, ih (c ^ p) hcp, ← Function.iterate_succ_apply' (⇑VV), ← pow_mul, ← pow_succ']

omit [CharP R p] in
theorem cross_wd2 (y y' : R) (hyy' : y * y' = 0) (c : R) (hcy : ∃ e, c = y * e) (a b : ℕ) :
    WittVector.teichmuller p (c ^ p ^ a) *
      ((⇑(WittVector.frobenius (p := p) (R := R)))^[b]
        (WittVector.frobenius (WittVector.frobenius (WittVector.teichmuller p y')) - WittVector.teichmuller p y')) = 0 := by
  obtain ⟨e, rfl⟩ := hcy
  have hiter : ∀ (x : R) (k : ℕ), ((⇑(WittVector.frobenius (p := p) (R := R)))^[k] (WittVector.teichmuller p x)) =
      WittVector.teichmuller p (x ^ p ^ k) := by
    intro x k
    induction k with
    | zero => simp
    | succ k ih => rw [Function.iterate_succ_apply', ih, WittVector.frobenius_teichmuller_eq, ← pow_mul, pow_succ]
  have hsub : ∀ k : ℕ, ((⇑(WittVector.frobenius (p := p) (R := R)))^[k]
      (WittVector.frobenius (WittVector.frobenius (WittVector.teichmuller p y')) - WittVector.teichmuller p y')) =
      WittVector.teichmuller p (y' ^ p ^ (k + 2)) - WittVector.teichmuller p (y' ^ p ^ k) := by
    intro k
    rw [(iterF_wittSub k), WittVector.frobenius_teichmuller_eq, WittVector.frobenius_teichmuller_eq, hiter, hiter, ← pow_mul,
      ← pow_mul, ← pow_succ', ← pow_succ']
  rw [hsub, mul_sub, ← map_mul, ← map_mul]
  have hz : ∀ m k : ℕ, (y * e) ^ p ^ m * y' ^ p ^ k = 0 := by
    intro m k
    have hm : 1 ≤ p ^ m := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
    have hk : 1 ≤ p ^ k := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
    obtain ⟨m', hm'⟩ := Nat.exists_eq_add_of_le hm
    obtain ⟨k', hk'⟩ := Nat.exists_eq_add_of_le hk
    rw [hm', hk', pow_add, pow_one, pow_add, pow_one]
    calc y * e * (y * e) ^ m' * (y' * y' ^ k') = (y * y') * (e * (y * e) ^ m' * y' ^ k') := by ring
      _ = 0 := by rw [hyy', zero_mul]
  rw [hz, hz, WittVector.teichmuller_zero, sub_self]
where
  iterF_wittSub (k : ℕ) : ∀ (a b : WittVector p R), ((⇑(WittVector.frobenius (p := p) (R := R)))^[k] (a - b)) =
      ((⇑(WittVector.frobenius (p := p) (R := R)))^[k] a) - ((⇑(WittVector.frobenius (p := p) (R := R)))^[k] b) := by
    intro a b
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, map_sub, Function.iterate_succ_apply', Function.iterate_succ_apply']

end exact
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_exists_hom_map_eq_add_verschiebungInt_of_endAct_varpiEnd_eq_teichmuller.B29CMU P2MW.S_CerednikDrinfeld_FormalODModule_exists_hom_map_eq_add_verschiebungInt_of_endAct_varpiEnd_eq_teichmuller.B29R1c"

end B29H2
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_exists_hom_map_eq_add_verschiebungInt_of_endAct_varpiEnd_eq_teichmuller.B29CMU P2MW.S_CerednikDrinfeld_FormalODModule_exists_hom_map_eq_add_verschiebungInt_of_endAct_varpiEnd_eq_teichmuller.B29R1c"

namespace B29H2

open CerednikDrinfeld MvFormalGroup MvFormalGroup.CartierModule B29R1c

section digits

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [CharP R p] {d : ℕ} {Φ : MvFormalGroup d R} [Φ.IsComm]

local notation "VV" => (verschiebungInt : CartierModule p Φ →+ CartierModule p Φ)
local notation "FF" => (MvFormalGroup.CartierModule.frobenius : CartierModule p Φ →+ CartierModule p Φ)

noncomputable abbrev W2 (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] (y : R) : WittVector p R :=
  WittVector.frobenius (WittVector.frobenius (WittVector.teichmuller p y)) - WittVector.teichmuller p y

theorem digits_form (x0 x1 : CartierModule p Φ) (y y' : R) (hyy' : y * y' = 0)
    (hF0 : FF x0 = W2 p y • x1 + VV x0) (hF1 : FF x1 = W2 p y' • x0 + VV x1) (N : ℕ) :
    ∃ h : CartierModule p Φ, FF x0 =
      (∑ n ∈ Finset.range N, (⇑VV)^[2 * n] (homothety (wd2 p y n ^ p ^ n) x1)) + VV x0 + (⇑VV)^[N] h := by
  obtain ⟨w', hw'⟩ := WittVector.exists_eq_sum_iterate_verschiebung_teichmuller_add p (W2 p y) N
  refine ⟨w' • (⇑FF)^[N] x1, ?_⟩
  rw [hF0]
  conv_lhs => rw [hw']
  rw [add_smul, Finset.sum_smul, iterVW_smul]
  have hterm : ∀ n ∈ Finset.range N,
      ((⇑(WittVector.verschiebung : WittVector p R →+ WittVector p R))^[n] (WittVector.teichmuller p ((W2 p y).coeff n))) • x1 =
        (⇑VV)^[2 * n] (homothety (wd2 p y n ^ p ^ n) x1) := by
    intro n _
    rw [iterVW_smul, show (W2 p y).coeff n = wd2 p y n from rfl,
      teichmuller_smul_iterF x0 x1 (W2 p y') hF1 n (wd2 p y n)
        (fun a b => cross_wd2 y y' hyy' _ (exists_wd2_eq_mul (p := p) y n) a b),
      ← Function.iterate_add_apply, ← two_mul, teichmuller_smul]
  rw [Finset.sum_congr rfl hterm]
  abel

end digits
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_exists_hom_map_eq_add_verschiebungInt_of_endAct_varpiEnd_eq_teichmuller.B29CMU P2MW.S_CerednikDrinfeld_FormalODModule_exists_hom_map_eq_add_verschiebungInt_of_endAct_varpiEnd_eq_teichmuller.B29R1c"

end B29H2
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_exists_hom_map_eq_add_verschiebungInt_of_endAct_varpiEnd_eq_teichmuller.B29CMU P2MW.S_CerednikDrinfeld_FormalODModule_exists_hom_map_eq_add_verschiebungInt_of_endAct_varpiEnd_eq_teichmuller.B29R1c"

namespace B29H2

open CerednikDrinfeld MvFormalGroup MvFormalGroup.CartierModule B29R1c

noncomputable def cH (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] (ys : Fin 2 → R) : ℕ → Fin 2 → Fin 2 → R :=
  fun m i k => if m = 1 ∧ k = i then 1 else if m % 2 = 0 ∧ k ≠ i then wd2 p (ys i) (m / 2) ^ p ^ (m / 2) else 0

section pack

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] {d : ℕ} {Φ : MvFormalGroup d R} [Φ.IsComm]

local notation "VV" => (verschiebungInt : CartierModule p Φ →+ CartierModule p Φ)
local notation "FF" => (MvFormalGroup.CartierModule.frobenius : CartierModule p Φ →+ CartierModule p Φ)

theorem inner_cH_0 (ys : Fin 2 → R) (x : Fin 2 → CartierModule p Φ) (m : ℕ) :
    (∑ k : Fin 2, homothety (cH p ys m 0 k) (x k)) =
      (if m = 1 then x 0 else 0) + (if m % 2 = 0 then homothety (wd2 p (ys 0) (m / 2) ^ p ^ (m / 2)) (x 1) else 0) := by
  rw [Fin.sum_univ_two]
  simp only [cH]
  by_cases h1 : m = 1
  · subst h1; simp [homothety_one, homothety_zero_left]
  · by_cases h2 : m % 2 = 0
    · simp [h1, h2, homothety_zero_left]
    · simp [h1, h2, homothety_zero_left]

theorem pack_0 (ys : Fin 2 → R) (x : Fin 2 → CartierModule p Φ) (M : ℕ) :
    (∑ m ∈ Finset.range M, (⇑VV)^[m] (∑ k : Fin 2, homothety (cH p ys m 0 k) (x k))) =
      (if 1 < M then VV (x 0) else 0) +
        ∑ n ∈ Finset.range M, (if 2 * n < M then (⇑VV)^[2 * n] (homothety (wd2 p (ys 0) n ^ p ^ n) (x 1)) else 0) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, ih, inner_cH_0, iterV_add, Finset.sum_range_succ]
    rcases Nat.eq_zero_or_pos M with hM0 | hM0
    · subst hM0; simp
    · have hshift : (∑ n ∈ Finset.range M,
          (if 2 * n < M + 1 then (⇑VV)^[2 * n] (homothety (wd2 p (ys 0) n ^ p ^ n) (x 1)) else 0)) =
          (∑ n ∈ Finset.range M,
            (if 2 * n < M then (⇑VV)^[2 * n] (homothety (wd2 p (ys 0) n ^ p ^ n) (x 1)) else 0)) +
          (⇑VV)^[M] (if M % 2 = 0 then homothety (wd2 p (ys 0) (M / 2) ^ p ^ (M / 2)) (x 1) else 0) := by
        by_cases hM : M % 2 = 0
        · have hmem : M / 2 ∈ Finset.range M := Finset.mem_range.2 (by omega)
          rw [if_pos hM, ← Finset.sum_erase_add _ _ hmem, ← Finset.sum_erase_add (Finset.range M) _ hmem,
            if_pos (show 2 * (M / 2) < M + 1 by omega), if_neg (show ¬ 2 * (M / 2) < M by omega), add_zero,
            show 2 * (M / 2) = M by omega]
          congr 1
          refine Finset.sum_congr rfl fun n hn => ?_
          have hne : n ≠ M / 2 := (Finset.mem_erase.1 hn).1
          have : (2 * n < M + 1) ↔ (2 * n < M) := by constructor <;> intro h <;> omega
          simp only [this]
        · rw [if_neg hM, Function.iterate_fixed (map_zero _) M, add_zero]
          refine Finset.sum_congr rfl fun n hn => ?_
          have : (2 * n < M + 1) ↔ (2 * n < M) := by constructor <;> intro h <;> omega
          simp only [this]
      have hlast : (if 2 * M < M + 1 then (⇑VV)^[2 * M] (homothety (wd2 p (ys 0) M ^ p ^ M) (x 1)) else 0) = 0 :=
        if_neg (by omega)
      have hA : (if 1 < M + 1 then VV (x 0) else 0) = (if 1 < M then VV (x 0) else 0) + (⇑VV)^[M] (if M = 1 then x 0 else 0) := by
        by_cases h1 : M = 1
        · subst h1; simp
        · rw [if_neg h1, if_pos (by omega), if_pos (by omega), Function.iterate_fixed (map_zero _) M, add_zero]
      rw [hshift, hlast, hA]
      have e : ∀ A B P Q : CartierModule p Φ, A + B + (P + Q) = A + P + (B + Q + 0) := by intros; abel
      exact e _ _ _ _

theorem inner_cH_1 (ys : Fin 2 → R) (x : Fin 2 → CartierModule p Φ) (m : ℕ) :
    (∑ k : Fin 2, homothety (cH p ys m 1 k) (x k)) =
      (if m = 1 then x 1 else 0) + (if m % 2 = 0 then homothety (wd2 p (ys 1) (m / 2) ^ p ^ (m / 2)) (x 0) else 0) := by
  rw [Fin.sum_univ_two]
  simp only [cH]
  by_cases h1 : m = 1
  · subst h1; simp [homothety_one, homothety_zero_left]
  · by_cases h2 : m % 2 = 0
    · simp [h1, h2, homothety_zero_left, add_comm]
    · simp [h1, h2, homothety_zero_left]

theorem pack_1 (ys : Fin 2 → R) (x : Fin 2 → CartierModule p Φ) (M : ℕ) :
    (∑ m ∈ Finset.range M, (⇑VV)^[m] (∑ k : Fin 2, homothety (cH p ys m 1 k) (x k))) =
      (if 1 < M then VV (x 1) else 0) +
        ∑ n ∈ Finset.range M, (if 2 * n < M then (⇑VV)^[2 * n] (homothety (wd2 p (ys 1) n ^ p ^ n) (x 0)) else 0) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, ih, inner_cH_1, iterV_add, Finset.sum_range_succ]
    rcases Nat.eq_zero_or_pos M with hM0 | hM0
    · subst hM0; simp
    · have hshift : (∑ n ∈ Finset.range M,
          (if 2 * n < M + 1 then (⇑VV)^[2 * n] (homothety (wd2 p (ys 1) n ^ p ^ n) (x 0)) else 0)) =
          (∑ n ∈ Finset.range M,
            (if 2 * n < M then (⇑VV)^[2 * n] (homothety (wd2 p (ys 1) n ^ p ^ n) (x 0)) else 0)) +
          (⇑VV)^[M] (if M % 2 = 0 then homothety (wd2 p (ys 1) (M / 2) ^ p ^ (M / 2)) (x 0) else 0) := by
        by_cases hM : M % 2 = 0
        · have hmem : M / 2 ∈ Finset.range M := Finset.mem_range.2 (by omega)
          rw [if_pos hM, ← Finset.sum_erase_add _ _ hmem, ← Finset.sum_erase_add (Finset.range M) _ hmem,
            if_pos (show 2 * (M / 2) < M + 1 by omega), if_neg (show ¬ 2 * (M / 2) < M by omega), add_zero,
            show 2 * (M / 2) = M by omega]
          congr 1
          refine Finset.sum_congr rfl fun n hn => ?_
          have hne : n ≠ M / 2 := (Finset.mem_erase.1 hn).1
          have : (2 * n < M + 1) ↔ (2 * n < M) := by constructor <;> intro h <;> omega
          simp only [this]
        · rw [if_neg hM, Function.iterate_fixed (map_zero _) M, add_zero]
          refine Finset.sum_congr rfl fun n hn => ?_
          have : (2 * n < M + 1) ↔ (2 * n < M) := by constructor <;> intro h <;> omega
          simp only [this]
      have hlast : (if 2 * M < M + 1 then (⇑VV)^[2 * M] (homothety (wd2 p (ys 1) M ^ p ^ M) (x 0)) else 0) = 0 :=
        if_neg (by omega)
      have hA : (if 1 < M + 1 then VV (x 1) else 0) = (if 1 < M then VV (x 1) else 0) + (⇑VV)^[M] (if M = 1 then x 1 else 0) := by
        by_cases h1 : M = 1
        · subst h1; simp
        · rw [if_neg h1, if_pos (by omega), if_pos (by omega), Function.iterate_fixed (map_zero _) M, add_zero]
      rw [hshift, hlast, hA]
      have e : ∀ A B P Q : CartierModule p Φ, A + B + (P + Q) = A + P + (B + Q + 0) := by intros; abel
      exact e _ _ _ _

end pack
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_exists_hom_map_eq_add_verschiebungInt_of_endAct_varpiEnd_eq_teichmuller.B29CMU P2MW.S_CerednikDrinfeld_FormalODModule_exists_hom_map_eq_add_verschiebungInt_of_endAct_varpiEnd_eq_teichmuller.B29R1c"

end B29H2
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_exists_hom_map_eq_add_verschiebungInt_of_endAct_varpiEnd_eq_teichmuller.B29CMU P2MW.S_CerednikDrinfeld_FormalODModule_exists_hom_map_eq_add_verschiebungInt_of_endAct_varpiEnd_eq_teichmuller.B29R1c"

namespace B29H2

open CerednikDrinfeld MvFormalGroup MvFormalGroup.CartierModule B29R1c

section expand

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [CharP R p] {d : ℕ} {Φ : MvFormalGroup d R} [Φ.IsComm]

local notation "VV" => (verschiebungInt : CartierModule p Φ →+ CartierModule p Φ)
local notation "FF" => (MvFormalGroup.CartierModule.frobenius : CartierModule p Φ →+ CartierModule p Φ)

omit [CharP R p] in

theorem fold (N : ℕ) (T : ℕ → CartierModule p Φ) : ∃ r : CartierModule p Φ,
    (∑ n ∈ Finset.range N, (⇑VV)^[2 * n] (T n)) =
      (∑ n ∈ Finset.range N, (if 2 * n < N then (⇑VV)^[2 * n] (T n) else 0)) + (⇑VV)^[N] r := by
  refine ⟨∑ n ∈ Finset.range N, (if 2 * n < N then 0 else (⇑VV)^[2 * n - N] (T n)), ?_⟩
  rw [show (⇑VV)^[N] (∑ n ∈ Finset.range N, (if 2 * n < N then (0 : CartierModule p Φ) else (⇑VV)^[2 * n - N] (T n))) =
      ∑ n ∈ Finset.range N, (⇑VV)^[N] (if 2 * n < N then 0 else (⇑VV)^[2 * n - N] (T n)) from
      map_sum (iterV (p := p) (Φ := Φ) N) _ _, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  split_ifs with h
  · rw [iterV_zero, add_zero]
  · rw [zero_add, ← Function.iterate_add_apply, Nat.add_sub_cancel' (Nat.le_of_not_lt h)]

omit [CharP R p] in
theorem vfold (N : ℕ) (z : CartierModule p Φ) : ∃ c : CartierModule p Φ,
    VV z = (if 1 < N then VV z else 0) + (⇑VV)^[N] c := by
  rcases Nat.lt_or_ge 1 N with h | h
  · exact ⟨0, by rw [if_pos h, iterV_zero, add_zero]⟩
  · rcases Nat.eq_zero_or_pos N with h0 | h0
    · subst h0; exact ⟨VV z, by simp⟩
    · have : N = 1 := by omega
      subst this; exact ⟨z, by simp⟩

theorem expand_0 (x : Fin 2 → CartierModule p Φ) (η ξ : R) (hξη : ξ * η = 0)
    (hF0 : FF (x 0) = W2 p η • x 1 + VV (x 0)) (hF1 : FF (x 1) = W2 p ξ • x 0 + VV (x 1)) (N : ℕ) :
    ∃ h : CartierModule p Φ, FF (x 0) =
      (∑ m : Fin N, (⇑VV)^[(m : ℕ)] (∑ k : Fin 2, homothety (cH p ![η, ξ] m 0 k) (x k))) + (⇑VV)^[N] h := by
  obtain ⟨h, hh⟩ := digits_form (x 0) (x 1) η ξ (by rw [mul_comm]; exact hξη) hF0 hF1 N
  rw [Fin.sum_univ_eq_sum_range (fun m => (⇑VV)^[m] (∑ k : Fin 2, homothety (cH p ![η, ξ] m 0 k) (x k))) N, pack_0]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  obtain ⟨r, hr⟩ := fold (p := p) (Φ := Φ) N (fun n => homothety (wd2 p η n ^ p ^ n) (x 1))
  obtain ⟨c, hc⟩ := vfold (p := p) (Φ := Φ) N (x 0)
  refine ⟨r + c + h, ?_⟩
  rw [hh, hr, iterV_add, iterV_add]
  nth_rewrite 1 [hc]
  have e : ∀ A B C D E : CartierModule p Φ, A + B + (C + D) + E = C + A + (B + D + E) := by intros; abel
  exact e _ _ _ _ _

theorem expand_1 (x : Fin 2 → CartierModule p Φ) (η ξ : R) (hξη : ξ * η = 0)
    (hF0 : FF (x 0) = W2 p η • x 1 + VV (x 0)) (hF1 : FF (x 1) = W2 p ξ • x 0 + VV (x 1)) (N : ℕ) :
    ∃ h : CartierModule p Φ, FF (x 1) =
      (∑ m : Fin N, (⇑VV)^[(m : ℕ)] (∑ k : Fin 2, homothety (cH p ![η, ξ] m 1 k) (x k))) + (⇑VV)^[N] h := by
  obtain ⟨h, hh⟩ := digits_form (x 1) (x 0) ξ η hξη hF1 hF0 N
  rw [Fin.sum_univ_eq_sum_range (fun m => (⇑VV)^[m] (∑ k : Fin 2, homothety (cH p ![η, ξ] m 1 k) (x k))) N, pack_1]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  obtain ⟨r, hr⟩ := fold (p := p) (Φ := Φ) N (fun n => homothety (wd2 p ξ n ^ p ^ n) (x 0))
  obtain ⟨c, hc⟩ := vfold (p := p) (Φ := Φ) N (x 1)
  refine ⟨r + c + h, ?_⟩
  rw [hh, hr, iterV_add, iterV_add]
  nth_rewrite 1 [hc]
  have e : ∀ A B C D E : CartierModule p Φ, A + B + (C + D) + E = C + A + (B + D + E) := by intros; abel
  exact e _ _ _ _ _

end expand
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_exists_hom_map_eq_add_verschiebungInt_of_endAct_varpiEnd_eq_teichmuller.B29CMU P2MW.S_CerednikDrinfeld_FormalODModule_exists_hom_map_eq_add_verschiebungInt_of_endAct_varpiEnd_eq_teichmuller.B29R1c"

end B29H2
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_exists_hom_map_eq_add_verschiebungInt_of_endAct_varpiEnd_eq_teichmuller.B29CMU P2MW.S_CerednikDrinfeld_FormalODModule_exists_hom_map_eq_add_verschiebungInt_of_endAct_varpiEnd_eq_teichmuller.B29R1c"

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
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_exists_hom_map_eq_add_verschiebungInt_of_endAct_varpiEnd_eq_teichmuller.B29CMU P2MW.S_CerednikDrinfeld_FormalODModule_exists_hom_map_eq_add_verschiebungInt_of_endAct_varpiEnd_eq_teichmuller.B29R1c"

namespace B29H2

open CerednikDrinfeld MvFormalGroup MvFormalGroup.CartierModule B29R1c B29R1

section dag

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [CharP R p] (Y : FormalODModule p R)

theorem core_dag (d0 d1 : CartierModule p Y.F) (u v : WittVector p R)
    (hPd0 : endAct Y.varpiEnd d0 = verschiebungInt d0) (hPd1 : endAct Y.varpiEnd d1 = verschiebungInt d1)
    (hFd0 : frobenius d0 = verschiebungInt d0) (hFd1 : frobenius d1 = verschiebungInt d1)
    (huv : ∀ a b : ℕ, ((⇑(WittVector.frobenius (p := p) (R := R)))^[a] u) *
      ((⇑(WittVector.frobenius (p := p) (R := R)))^[b] v) = 0) :
    frobenius ((p : WittVector p R) • d0 + WittVector.frobenius u • verschiebungInt d1) =
      (WittVector.frobenius (WittVector.frobenius u) - u) • ((p : WittVector p R) • d1 + WittVector.frobenius v • verschiebungInt d0) +
        verschiebungInt ((p : WittVector p R) • d0 + WittVector.frobenius u • verschiebungInt d1) ∧
    endAct Y.varpiEnd ((p : WittVector p R) • d0 + WittVector.frobenius u • verschiebungInt d1) =
      (WittVector.frobenius u - u) • ((p : WittVector p R) • d1 + WittVector.frobenius v • verschiebungInt d0) +
        verschiebungInt ((p : WittVector p R) • d0 + WittVector.frobenius u • verschiebungInt d1) := by
  have hσp : WittVector.frobenius (p : WittVector p R) = p := map_natCast _ p
  have cx : ∀ a a' b : ℕ, (((⇑(WittVector.frobenius (p := p) (R := R)))^[a] u) - ((⇑(WittVector.frobenius (p := p) (R := R)))^[a'] u)) *
      ((⇑(WittVector.frobenius (p := p) (R := R)))^[b] v) = 0 := by
    intro a a' b; rw [sub_mul, huv, huv, sub_zero]
  have c21 : (WittVector.frobenius (WittVector.frobenius u) - u) * WittVector.frobenius v = 0 := cx 2 0 1
  have c11 : (WittVector.frobenius u - u) * WittVector.frobenius v = 0 := cx 1 0 1
  have hpd1 : (p : WittVector p R) • d1 = verschiebungInt (verschiebungInt d1) := by rw [← VF_eq Y d1, hFd1]
  have e1 : verschiebungInt ((p : WittVector p R) • d0) = (p : WittVector p R) • verschiebungInt d0 := by
    rw [smul_verschiebungInt, hσp]
  have e2 : verschiebungInt (WittVector.frobenius u • verschiebungInt d1) = u • verschiebungInt (verschiebungInt d1) :=
    (smul_verschiebungInt u (verschiebungInt d1)).symm
  refine ⟨?_, ?_⟩
  · rw [map_add, frobenius_smul, frobenius_smul, hσp, hFd0, frobenius_verschiebungInt_eq_smul, map_add, e1, e2, smul_add,
      ← mul_smul (WittVector.frobenius (WittVector.frobenius u) - u) (WittVector.frobenius v), c21, zero_smul, add_zero, hpd1,
      sub_smul]
    abel
  · rw [map_add, endAct_smul_witt, endAct_smul_witt, hPd0, endAct_verschiebungInt, hPd1, map_add, e1, e2, smul_add,
      ← mul_smul (WittVector.frobenius u - u) (WittVector.frobenius v), c11, zero_smul, add_zero, hpd1, sub_smul]
    abel

end dag
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_exists_hom_map_eq_add_verschiebungInt_of_endAct_varpiEnd_eq_teichmuller.B29CMU P2MW.S_CerednikDrinfeld_FormalODModule_exists_hom_map_eq_add_verschiebungInt_of_endAct_varpiEnd_eq_teichmuller.B29R1c"

end B29H2
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_exists_hom_map_eq_add_verschiebungInt_of_endAct_varpiEnd_eq_teichmuller.B29CMU P2MW.S_CerednikDrinfeld_FormalODModule_exists_hom_map_eq_add_verschiebungInt_of_endAct_varpiEnd_eq_teichmuller.B29R1c"

open CerednikDrinfeld MvFormalGroup MvFormalGroup.CartierModule B29CMU B29R1 B29R1c B29R1asm B29H2 in
theorem solution
    (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] [CharP R p] (j : Zp2 p →+* R)
    (ξ η : R) (hξη : ξ * η = 0)
    (Y X : FormalODModule p R) (hYs : Y.IsSpecial j) (hXs : X.IsSpecial j)
    (δ : Fin 2 → CartierModule p Y.F) (hδ : Y.IsHomogeneousVBasis j δ)
    (hδ0 : endAct Y.varpiEnd (δ 0) = verschiebungInt (δ 0))
    (hδ1 : endAct Y.varpiEnd (δ 1) = verschiebungInt (δ 1))
    (γ : Fin 2 → CartierModule p X.F) (hγ : X.IsHomogeneousVBasis j γ)
    (hγ0 : endAct X.varpiEnd (γ 0) =
      (WittVector.teichmuller p (η ^ p) - WittVector.teichmuller p η) • γ 1 + verschiebungInt (γ 0))
    (hγ1 : endAct X.varpiEnd (γ 1) =
      (WittVector.teichmuller p (ξ ^ p) - WittVector.teichmuller p ξ) • γ 0 + verschiebungInt (γ 1)) :
    ∃ ρ : FormalODModule.Hom X Y,
      CartierModule.map ρ.toLawHom (γ 0) =
          (p : WittVector p R) • δ 0 + verschiebungInt (WittVector.teichmuller p (η ^ p ^ 2) • δ 1) ∧
      CartierModule.map ρ.toLawHom (γ 1) =
          (p : WittVector p R) • δ 1 + verschiebungInt (WittVector.teichmuller p (ξ ^ p ^ 2) • δ 0) := by
  letI : Algebra (PadicInt p) R := algebraPadicInt j
  have hVY := verschiebungInt_injective_of_algebra_padicInt p Y.F
  have hVX := verschiebungInt_injective_of_algebra_padicInt p X.F
  set u : WittVector p R := WittVector.teichmuller p η with hu
  set v : WittVector p R := WittVector.teichmuller p ξ with hv
  have hiter : ∀ (x : R) (a : ℕ), ((⇑(WittVector.frobenius (p := p) (R := R)))^[a] (WittVector.teichmuller p x)) =
      WittVector.teichmuller p (x ^ p ^ a) := by
    intro x a
    induction a with
    | zero => simp
    | succ a ih => rw [Function.iterate_succ_apply', ih, WittVector.frobenius_teichmuller_eq, ← pow_mul, pow_succ]
  have hpow : ∀ a b : ℕ, η ^ p ^ a * ξ ^ p ^ b = 0 := by
    intro a b
    have ha : 1 ≤ p ^ a := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
    have hb : 1 ≤ p ^ b := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
    obtain ⟨a', ha'⟩ := Nat.exists_eq_add_of_le ha
    obtain ⟨b', hb'⟩ := Nat.exists_eq_add_of_le hb
    rw [ha', hb', pow_add, pow_add, pow_one, pow_one]
    calc η * η ^ a' * (ξ * ξ ^ b') = (ξ * η) * (η ^ a' * ξ ^ b') := by ring
      _ = 0 := by rw [hξη, zero_mul]
  have huv : ∀ a b : ℕ, ((⇑(WittVector.frobenius (p := p) (R := R)))^[a] u) *
      ((⇑(WittVector.frobenius (p := p) (R := R)))^[b] v) = 0 := by
    intro a b; rw [hu, hv, hiter, hiter, ← map_mul, hpow, WittVector.teichmuller_zero]
  have hvu : ∀ a b : ℕ, ((⇑(WittVector.frobenius (p := p) (R := R)))^[a] v) *
      ((⇑(WittVector.frobenius (p := p) (R := R)))^[b] u) = 0 := by
    intro a b; rw [mul_comm]; exact huv b a
  have hσu : WittVector.frobenius u = WittVector.teichmuller p (η ^ p) := by rw [hu, WittVector.frobenius_teichmuller_eq]
  have hσv : WittVector.frobenius v = WittVector.teichmuller p (ξ ^ p) := by rw [hv, WittVector.frobenius_teichmuller_eq]
  have hγ0' : endAct X.varpiEnd (γ 0) = (WittVector.frobenius u - u) • γ 1 + verschiebungInt (γ 0) := by rw [hσu]; exact hγ0
  have hγ1' : endAct X.varpiEnd (γ 1) = (WittVector.frobenius v - v) • γ 0 + verschiebungInt (γ 1) := by rw [hσv]; exact hγ1

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

  have hFγ0 : frobenius (γ 0) = W2 p η • γ 1 + verschiebungInt (γ 0) := by
    have := frob_gamma0 X γ u v hγ0' hγ1' huv hVX; rw [hu] at this; exact this
  have hFγ1 : frobenius (γ 1) = W2 p ξ • γ 0 + verschiebungInt (γ 1) := by
    have := frob_gamma1 X γ u v hγ0' hγ1' huv hVX; rw [hv] at this; exact this

  set n : Fin 2 → CartierModule p Y.F :=
    ![(p : WittVector p R) • δ 0 + WittVector.frobenius u • verschiebungInt (δ 1),
      (p : WittVector p R) • δ 1 + WittVector.frobenius v • verschiebungInt (δ 0)] with hn
  have hn0 : n 0 = (p : WittVector p R) • δ 0 + WittVector.frobenius u • verschiebungInt (δ 1) := rfl
  have hn1 : n 1 = (p : WittVector p R) • δ 1 + WittVector.frobenius v • verschiebungInt (δ 0) := rfl
  obtain ⟨hFn0, hPn0⟩ := core_dag Y (δ 0) (δ 1) u v hδ0 hδ1 hFδ0 hFδ1 huv
  obtain ⟨hFn1, hPn1⟩ := core_dag Y (δ 1) (δ 0) v u hδ1 hδ0 hFδ1 hFδ0 hvu
  have hFn0' : frobenius (n 0) = W2 p η • n 1 + verschiebungInt (n 0) := by rw [hn0, hn1, hFn0, hu]
  have hFn1' : frobenius (n 1) = W2 p ξ • n 0 + verschiebungInt (n 1) := by rw [hn0, hn1, hFn1, hv]

  have hF : ∀ (i : Fin 2) (N : ℕ), ∃ h : CartierModule p X.F, frobenius (γ i) =
      (∑ m : Fin N, (⇑(verschiebungInt (p := p) (Φ := X.F)))^[(m : ℕ)]
        (∑ k : Fin 2, homothety (cH p ![η, ξ] m i k) (γ k))) +
      (⇑(verschiebungInt (p := p) (Φ := X.F)))^[N] h := by
    intro i N; fin_cases i
    · exact expand_0 γ η ξ hξη hFγ0 hFγ1 N
    · exact expand_1 γ η ξ hξη hFγ0 hFγ1 N
  have hF' : ∀ (i : Fin 2) (N : ℕ), ∃ h : CartierModule p Y.F, frobenius (n i) =
      (∑ m : Fin N, (⇑(verschiebungInt (p := p) (Φ := Y.F)))^[(m : ℕ)]
        (∑ k : Fin 2, homothety (cH p ![η, ξ] m i k) (n k))) +
      (⇑(verschiebungInt (p := p) (Φ := Y.F)))^[N] h := by
    intro i N; fin_cases i
    · exact expand_0 n η ξ hξη hFn0' hFn1' N
    · exact expand_1 n η ξ hξη hFn0' hFn1' N
  obtain ⟨θ, ⟨hθγ, hθV, hθH, hθF⟩, -⟩ :=
    existsUnique_addMonoidHom_apply_eq_of_frobenius_expansion p X.F Y.F γ hγ.2 n (cH p ![η, ξ]) hF hF'

  obtain ⟨φ, hφ⟩ := exists_hom_forall_map_eq_of_algebra_padicInt p X.F Y.F θ hθF hθV hθH
  have hθW : ∀ (w : WittVector p R) f, θ (w • f) = w • θ f := by
    intro w f; rw [← hφ, ← hφ, map_smul_witt]

  have hPi : ∀ f, θ (endAct X.varpiEnd f) = endAct Y.varpiEnd (θ f) :=
    intertwine θ hθV hθH hθF γ hγ.2 (cH p ![η, ξ]) hF X.varpiEnd Y.varpiEnd (fun i => by
      fin_cases i
      · show θ (endAct X.varpiEnd (γ 0)) = endAct Y.varpiEnd (θ (γ 0))
        rw [hγ0', map_add, hθW, hθV, hθγ, hθγ, hn0, hn1, hPn0]
      · show θ (endAct X.varpiEnd (γ 1)) = endAct Y.varpiEnd (θ (γ 1))
        rw [hγ1', map_add, hθW, hθV, hθγ, hθγ, hn0, hn1, hPn1])

  have hmem : ∀ i : Fin 2, n i ∈ Y.gradedPiece j i := by
    have hg0 := hδ.1 0
    have hg1 := hδ.1 1
    intro i; fin_cases i
    · show n 0 ∈ Y.gradedPiece j 0
      rw [hn0]
      refine AddSubgroup.add_mem _ (Y.smul_mem_gradedPiece j _ _ _ hg0) (Y.smul_mem_gradedPiece j _ _ _ ?_)
      have := Y.verschiebungInt_mem_gradedPiece_succ j 1 (δ 1) hg1
      rwa [show (1 : ℕ) + 1 = 0 + 2 from rfl, Y.gradedPiece_add_two j 0] at this
    · show n 1 ∈ Y.gradedPiece j 1
      rw [hn1]
      refine AddSubgroup.add_mem _ (Y.smul_mem_gradedPiece j _ _ _ hg1) (Y.smul_mem_gradedPiece j _ _ _ ?_)
      exact Y.verschiebungInt_mem_gradedPiece_succ j 0 (δ 0) hg0
  have hT : ∀ (ζ : GaloisField p 2) (f : CartierModule p X.F),
      defect X Y θ (WittVector.teichmuller p ζ) f = 0 := by
    intro ζ
    have key := intertwine θ hθV hθH hθF γ hγ.2 (cH p ![η, ξ]) hF
      (X.actEnd (WittVector.teichmuller p ζ)) (Y.actEnd (WittVector.teichmuller p ζ)) (fun i => by
        rw [(X.mem_gradedPiece_iff j i (γ i)).mp (hγ.1 i) ζ, hθH, hθγ,
          (Y.mem_gradedPiece_iff j i (n i)).mp (hmem i) ζ])
    intro f
    rw [defect_apply, sub_eq_zero]
    exact key f
  have hsep : IsHausdorff (Ideal.span {(p : R)}) R := by
    have hp0 : (p : R) = 0 := CharP.cast_eq_zero R p
    rw [hp0, Ideal.span_singleton_eq_bot.mpr rfl]
    exact ⟨fun x hx => by simpa [SModEq.sub_mem] using hx 1⟩
  have hZp2 : ∀ (cc : Zp2 p) f, θ (endAct (X.actEnd cc) f) = endAct (Y.actEnd cc) (θ f) := by
    intro cc f
    have h0 := defect_eq_zero X Y θ hθV hθH hsep γ δ hγ.2 hδ.2 hT cc f
    rwa [defect_apply, sub_eq_zero] at h0
  have hact : ∀ a, φ.comp (X.actEnd a) = (Y.actEnd a).comp φ := by
    intro a
    refine eq_of_forall_map_eq_of_algebra_padicInt p X.F Y.F _ _ (fun f => ?_)
    rw [CartierModule.map_comp, CartierModule.map_comp, hφ, hφ, ← CartierModule.endAct_apply,
      ← CartierModule.endAct_apply, hZp2]
  have hvarpi : φ.comp X.varpiEnd = Y.varpiEnd.comp φ := by
    refine eq_of_forall_map_eq_of_algebra_padicInt p X.F Y.F _ _ (fun f => ?_)
    rw [CartierModule.map_comp, CartierModule.map_comp, hφ, hφ, ← CartierModule.endAct_apply,
      ← CartierModule.endAct_apply, hPi]
  refine ⟨toODHom φ hact hvarpi, ?_, ?_⟩
  · rw [toODHom_toLawHom, hφ, hθγ, hn0, smul_verschiebungInt, hσu, WittVector.frobenius_teichmuller_eq, ← pow_mul,
      ← pow_two]
  · rw [toODHom_toLawHom, hφ, hθγ, hn1, smul_verschiebungInt, hσv, WittVector.frobenius_teichmuller_eq, ← pow_mul,
      ← pow_two]

end S_CerednikDrinfeld_FormalODModule_exists_hom_map_eq_add_verschiebungInt_of_endAct_varpiEnd_eq_teichmuller
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_hom_map_eq_add_verschiebungInt_of_endAct_varpiEnd_eq_teichmuller (solution)
