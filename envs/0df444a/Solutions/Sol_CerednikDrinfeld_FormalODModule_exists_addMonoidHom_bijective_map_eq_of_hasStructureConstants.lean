-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_addMonoidHom_bijective_map_eq_of_hasStructureConstants
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/0bfbcbe4-36ff-5c09-9df5-4d5ee160ec68

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
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_forall_hasStructureConstants_frobenius_eq_sum
import Theorems.Thm_MvFormalGroup_CartierModule_existsUnique_addMonoidHom_apply_eq_of_frobenius_expansion
import Theorems.Thm_MvFormalGroup_CartierModule_existsUnique_eq_sum_verschiebungInt_iterate_homothety_add
import Theorems.Thm_MvFormalGroup_CartierModule_existsUnique_forall_eq_sum_range_verschiebungInt_iterate_add
import Theorems.Thm_MvFormalGroup_CartierModule_verschiebungInt_injective_of_algebra_padicInt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_addMonoidHom_bijective_map_eq_of_hasStructureConstants
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply"

set_option autoImplicit false

universe u

open MvFormalGroup MvFormalGroup.CartierModule

namespace CMUnique

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

end CMUnique
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_exists_addMonoidHom_bijective_map_eq_of_hasStructureConstants.CMUnique"

open MvFormalGroup MvFormalGroup.CartierModule CMUnique

open CerednikDrinfeld in

theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B] (j : CerednikDrinfeld.Zp2 p →+* B)
    (hsep : IsHausdorff (Ideal.span {(p : B)}) B)
    (X X' : CerednikDrinfeld.FormalODModule p B)
    (γ : Fin 2 → MvFormalGroup.CartierModule p X.F)
    (γ' : Fin 2 → MvFormalGroup.CartierModule p X'.F)
    (hγ : X.IsHomogeneousVBasis j γ) (hγ' : X'.IsHomogeneousVBasis j γ')
    (a : ℕ → Fin 2 → B)
    (ha : X.HasStructureConstants γ a) (ha' : X'.HasStructureConstants γ' a) :
    ∃ θ : MvFormalGroup.CartierModule p X.F →+ MvFormalGroup.CartierModule p X'.F,
      Function.Bijective θ ∧ (∀ i : Fin 2, θ (γ i) = γ' i) ∧
      (∀ f, θ (MvFormalGroup.CartierModule.frobenius f) =
        MvFormalGroup.CartierModule.frobenius (θ f)) ∧
      (∀ f, θ (MvFormalGroup.CartierModule.verschiebungInt f) =
        MvFormalGroup.CartierModule.verschiebungInt (θ f)) ∧
      (∀ (b : B) f, θ (MvFormalGroup.CartierModule.homothety b f) =
        MvFormalGroup.CartierModule.homothety b (θ f)) ∧
      (∀ (c : CerednikDrinfeld.Zp2 p) f,
        θ (MvFormalGroup.CartierModule.endAct (X.actEnd c) f) =
          MvFormalGroup.CartierModule.endAct (X'.actEnd c) (θ f)) ∧
      (∀ f, θ (MvFormalGroup.CartierModule.endAct X.varpiEnd f) =
        MvFormalGroup.CartierModule.endAct X'.varpiEnd (θ f)) := by
  letI : Algebra (PadicInt p) B := algebraPadicInt j

  obtain ⟨c, hc⟩ :=
    CerednikDrinfeld.FormalODModule.exists_forall_hasStructureConstants_frobenius_eq_sum p j a
  have hF := hc X γ hγ ha
  have hF' := hc X' γ' hγ' ha'

  obtain ⟨θ, ⟨hθγ, hθV, hθH, hθF⟩, -⟩ :=
    existsUnique_addMonoidHom_apply_eq_of_frobenius_expansion p X.F X'.F γ hγ.2 γ' c hF hF'
  obtain ⟨θ', ⟨hθ'γ, hθ'V, hθ'H, hθ'F⟩, -⟩ :=
    existsUnique_addMonoidHom_apply_eq_of_frobenius_expansion p X'.F X.F γ' hγ'.2 γ c hF' hF
  have huX := (existsUnique_addMonoidHom_apply_eq_of_frobenius_expansion p X.F X.F γ hγ.2 γ c hF hF).unique
    (y₁ := θ'.comp θ) (y₂ := AddMonoidHom.id _)
    ⟨fun i => by simp [hθγ, hθ'γ], fun f => by simp [hθV, hθ'V], fun b f => by simp [hθH, hθ'H],
      fun f => by simp [hθF, hθ'F]⟩
    ⟨fun i => rfl, fun f => rfl, fun b f => rfl, fun f => rfl⟩
  have huX' := (existsUnique_addMonoidHom_apply_eq_of_frobenius_expansion p X'.F X'.F γ' hγ'.2 γ' c hF' hF').unique
    (y₁ := θ.comp θ') (y₂ := AddMonoidHom.id _)
    ⟨fun i => by simp [hθγ, hθ'γ], fun f => by simp [hθV, hθ'V], fun b f => by simp [hθH, hθ'H],
      fun f => by simp [hθF, hθ'F]⟩
    ⟨fun i => rfl, fun f => rfl, fun b f => rfl, fun f => rfl⟩
  have hbij : Function.Bijective θ := by
    refine Function.bijective_iff_has_inverse.mpr ⟨θ', fun x => ?_, fun y => ?_⟩
    · exact congrArg (fun φ : CartierModule p X.F →+ CartierModule p X.F => φ x) huX
    · exact congrArg (fun φ : CartierModule p X'.F →+ CartierModule p X'.F => φ y) huX'

  have hPiγ : ∀ i, θ (endAct X.varpiEnd (γ i)) = endAct X'.varpiEnd (θ (γ i)) := by
    intro i
    rw [hθγ]
    refine eq_of_forall_sub_mem _ _ fun N => ?_
    obtain ⟨r, hr⟩ := ha i N
    obtain ⟨r', hr'⟩ := ha' i N
    refine ⟨θ r - r', ?_⟩
    rw [hr, hr', map_add, map_sum]
    simp only [map_iterate_V θ hθV, hθH, hθγ]
    rw [add_sub_add_left_eq_sub, iterate_V_sub]
  have hPi : ∀ f, θ (endAct X.varpiEnd f) = endAct X'.varpiEnd (θ f) :=
    intertwine θ hθV hθH hθF γ hγ.2 c hF X.varpiEnd X'.varpiEnd hPiγ

  have hT : ∀ (ζ : GaloisField p 2) (f : CartierModule p X.F),
      defect X X' θ (WittVector.teichmuller p ζ) f = 0 := by
    intro ζ
    have key := intertwine θ hθV hθH hθF γ hγ.2 c hF
      (X.actEnd (WittVector.teichmuller p ζ)) (X'.actEnd (WittVector.teichmuller p ζ)) (fun i => by
        rw [(X.mem_gradedPiece_iff j i (γ i)).mp (hγ.1 i) ζ, hθH, hθγ,
          (X'.mem_gradedPiece_iff j i (γ' i)).mp (hγ'.1 i) ζ])
    intro f
    rw [defect_apply, sub_eq_zero]
    exact key f
  have hZp2 : ∀ (cc : CerednikDrinfeld.Zp2 p) f,
      θ (endAct (X.actEnd cc) f) = endAct (X'.actEnd cc) (θ f) := by
    intro cc f
    have h0 := defect_eq_zero X X' θ hθV hθH hsep γ γ' hγ.2 hγ'.2 hT cc f
    rwa [defect_apply, sub_eq_zero] at h0
  exact ⟨θ, hbij, hθγ, hθF, hθV, hθH, hZp2, hPi⟩

end S_CerednikDrinfeld_FormalODModule_exists_addMonoidHom_bijective_map_eq_of_hasStructureConstants
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_addMonoidHom_bijective_map_eq_of_hasStructureConstants (solution)
