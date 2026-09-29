-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormalODModule.exists_addMonoidHom_cartierModule_injective_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/1a9e3cf3-8056-5370-be26-7670c046859b

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isCompl_gradedPiece_zero_one_of_isCompl_lieZero_lieOne
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_fin_two_endAct_varpiEnd_eq_verschiebung_of_isAlgClosed
import Theorems.Thm_MvFormalGroup_CartierModule_map_injective_of_finite_quotient
import Theorems.Thm_MvFormalGroup_CartierModule_existsUnique_forall_eq_sum_range_verschiebung_iterate_add
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_addMonoidHom_cartierModule_injective_of_isAlgClosed
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply"

set_option autoImplicit false

universe u

namespace P2mKcBC52Module

open MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld CerednikDrinfeld.FormalODModule

variable {p : ℕ} [hp : Fact p.Prime] {k : Type u} [Field k] [CharP k p]
variable {j : Zp2 p →+* k}

section OneModule

variable (X : SpecialFormalODModule p j)

omit [CharP k p] in
theorem smul_mem_gradedPiece (n : ℕ) (w : WittVector p k) (f : CartierModule p X.F)
    (hf : f ∈ X.toFormalODModule.gradedPiece j n) :
    w • f ∈ X.toFormalODModule.gradedPiece j n := by
  intro c
  have hfc := hf c
  rw [endAct_smul_witt, hfc, homothety_smul_witt]

def piece (n : ℕ) : Submodule (WittVector p k) (CartierModule p X.F) where
  carrier := X.toFormalODModule.gradedPiece j n
  add_mem' hf hg := (X.toFormalODModule.gradedPiece j n).add_mem hf hg
  zero_mem' := (X.toFormalODModule.gradedPiece j n).zero_mem
  smul_mem' w f hf := smul_mem_gradedPiece X n w f hf

omit [CharP k p] in
theorem mem_piece {n : ℕ} {f : CartierModule p X.F} :
    f ∈ piece X n ↔ f ∈ X.toFormalODModule.gradedPiece j n := Iff.rfl

omit [CharP k p] in
theorem mem_piece_add_two {n : ℕ} {f : CartierModule p X.F} :
    f ∈ piece X (n + 2) ↔ f ∈ piece X n := by
  rw [mem_piece, mem_piece, gradedPiece_add_two]

theorem grading :
    IsCompl (X.toFormalODModule.gradedPiece j 0) (X.toFormalODModule.gradedPiece j 1) ∧
    (∀ (n : ℕ) (g : CartierModule p X.F),
        verschiebung g ∈ X.toFormalODModule.gradedPiece j (n + 1) ↔
          g ∈ X.toFormalODModule.gradedPiece j n) ∧
    (∀ n, ∀ f ∈ X.toFormalODModule.gradedPiece j n,
        frobenius f ∈ X.toFormalODModule.gradedPiece j (n + 1)) ∧
    (∀ n, ∀ f ∈ X.toFormalODModule.gradedPiece j n,
        endAct X.varpiEnd f ∈ X.toFormalODModule.gradedPiece j (n + 1)) ∧
    (∀ (n : ℕ) (b : k), ∀ f ∈ X.toFormalODModule.gradedPiece j n,
        homothety b f ∈ X.toFormalODModule.gradedPiece j n) ∧
    (∀ (n : ℕ) (a : Zp2 p), ∀ f ∈ X.toFormalODModule.gradedPiece j n,
        endAct (X.actEnd a) f ∈ X.toFormalODModule.gradedPiece j n) ∧
    (X.toFormalODModule.gradedPiece j 0).map tangent = (X.lieZero j).toAddSubgroup ∧
    (X.toFormalODModule.gradedPiece j 1).map tangent = (X.lieOne j).toAddSubgroup :=
  isCompl_gradedPiece_zero_one_of_isCompl_lieZero_lieOne p j X.toFormalODModule X.isSpecial.1

theorem verschiebung_mem_iff (n : ℕ) (g : CartierModule p X.F) :
    verschiebung g ∈ piece X (n + 1) ↔ g ∈ piece X n :=
  (grading X).2.1 n g

private theorem _root_.P2mKcBC52Module.pi_mem (n : ℕ) {f : CartierModule p X.F} (hf : f ∈ piece X n) :
    endAct X.varpiEnd f ∈ piece X (n + 1) :=
  (grading X).2.2.2.1 n f hf

p2m_export "P2mKcBC52Module" "pi_mem"
theorem pi_mem' (n : ℕ) {f : CartierModule p X.F} (hf : f ∈ piece X (n + 1)) :
    endAct X.varpiEnd f ∈ piece X n := by
  rw [← mem_piece_add_two]
  exact pi_mem X (n + 1) hf

theorem verschiebung_mem' {f : CartierModule p X.F} (hf : f ∈ piece X 1) :
    verschiebung f ∈ piece X 0 := by
  rw [← mem_piece_add_two]
  exact (verschiebung_mem_iff X 1 f).mpr hf

theorem isCompl_piece : IsCompl (piece X 0) (piece X 1) := by
  have h := (grading X).1
  refine isCompl_iff.mpr ⟨?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro f hf0 hf1
    exact AddSubgroup.disjoint_def.mp h.disjoint hf0 hf1
  · rw [codisjoint_iff, Submodule.eq_top_iff']
    intro f
    have hsup : f ∈ X.toFormalODModule.gradedPiece j 0 ⊔ X.toFormalODModule.gradedPiece j 1 := by
      rw [codisjoint_iff.mp h.codisjoint]; trivial
    obtain ⟨y, hy, z, hz, hyz⟩ := AddSubgroup.mem_sup.mp hsup
    exact Submodule.mem_sup.mpr ⟨y, hy, z, hz, hyz⟩

noncomputable def pr0 : CartierModule p X.F →ₗ[WittVector p k] CartierModule p X.F :=
  (piece X 0).projection (piece X 1) (isCompl_piece X)

noncomputable def pr1 : CartierModule p X.F →ₗ[WittVector p k] CartierModule p X.F :=
  (piece X 1).projection (piece X 0) (isCompl_piece X).symm

theorem pr0_mem (m : CartierModule p X.F) : pr0 X m ∈ piece X 0 :=
  Submodule.projection_apply_mem _ m

theorem pr1_mem (m : CartierModule p X.F) : pr1 X m ∈ piece X 1 :=
  Submodule.projection_apply_mem _ m

theorem pr0_add_pr1 (m : CartierModule p X.F) : pr0 X m + pr1 X m = m :=
  Submodule.projection_add_projection_eq_self _ m

theorem pr0_of_add {a b : CartierModule p X.F} (ha : a ∈ piece X 0) (hb : b ∈ piece X 1) :
    pr0 X (a + b) = a := by
  rw [map_add, pr0, (Submodule.projection_eq_self_iff _ a).mpr ha,
    Submodule.projection_apply_of_mem_right _ hb, add_zero]

theorem pr1_of_add {a b : CartierModule p X.F} (ha : a ∈ piece X 0) (hb : b ∈ piece X 1) :
    pr1 X (a + b) = b := by
  rw [map_add, pr1, (Submodule.projection_eq_self_iff _ b).mpr hb,
    Submodule.projection_apply_of_mem_right _ ha, zero_add]

omit [CharP k p] in
theorem finite_kerAlgebra :
    Module.Finite k (MvPowerSeries (Fin 2) k ⧸ Ideal.span (Set.range (X.F.nthSeries p))) := by
  have h := X.hasHeight.2.2 k (RingHom.id k)
  have hmap : (X.act (p : Zp2 p)).map (RingHom.id k) = X.F.nthSeries p := by
    funext i
    show MvPowerSeries.map (RingHom.id k) (X.act (p : Zp2 p) i) = X.F.nthSeries p i
    rw [MvPowerSeries.map_id, ← X.act_natCast]
    rfl
  rw [hmap] at h
  exact Module.finite_of_finrank_pos (by rw [h]; exact pow_pos hp.out.pos 4)

omit [CharP k p] in

theorem smul_p_injective :
    Function.Injective (fun f : CartierModule p X.F => (p : WittVector p k) • f) := by
  have hinj : Function.Injective (map (p := p) ((p : ℕ) : MvFormalGroup.End X.F)) := by
    refine map_injective_of_finite_quotient p X.F X.F _ ?_
    rw [MvFormalGroup.End.toPowerSeries_natCast]
    exact finite_kerAlgebra X
  intro f g hfg
  apply hinj
  have hdict : ∀ x : CartierModule p X.F,
      (p : WittVector p k) • x = map ((p : ℕ) : MvFormalGroup.End X.F) x := fun x => by
    rw [natCast_smul_eq_nsmul', ← endAct_natCast]
    rfl
  have h' : (p : WittVector p k) • f = (p : WittVector p k) • g := hfg
  rwa [hdict, hdict] at h'

omit [CharP k p] in

theorem pi_pi (f : CartierModule p X.F) :
    endAct X.varpiEnd (endAct X.varpiEnd f) = (p : WittVector p k) • f := by
  have h : endAct X.varpiEnd (endAct X.varpiEnd f) = endAct (X.varpiEnd * X.varpiEnd) f := by
    rw [map_mul]; rfl
  rw [h, varpiEnd_mul_varpiEnd, map_natCast, endAct_natCast, natCast_smul_eq_nsmul']

omit [CharP k p] in
theorem pi_injective : Function.Injective (endAct X.varpiEnd : CartierModule p X.F → _) := by
  intro f g h
  apply smul_p_injective X
  show (p : WittVector p k) • f = (p : WittVector p k) • g
  rw [← pi_pi, ← pi_pi, h]

omit [CharP k p] in
theorem pi_smul (w : WittVector p k) (f : CartierModule p X.F) :
    endAct X.varpiEnd (w • f) = w • endAct X.varpiEnd f :=
  endAct_smul_witt _ w f

theorem pi_verschiebung (f : CartierModule p X.F) :
    endAct X.varpiEnd (verschiebung f) = verschiebung (endAct X.varpiEnd f) :=
  endAct_verschiebung _ f

theorem p_smul_verschiebung (f : CartierModule p X.F) :
    (p : WittVector p k) • verschiebung f = verschiebung ((p : WittVector p k) • f) := by
  rw [smul_verschiebung, map_natCast]

omit [CharP k p] in

theorem act_p_mul (a : Zp2 p) (f : CartierModule p X.F) :
    endAct (X.actEnd ((p : Zp2 p) * a)) f = (p : WittVector p k) • endAct (X.actEnd a) f := by
  have h : X.actEnd ((p : Zp2 p) * a) = (p : MvFormalGroup.End X.F) * X.actEnd a := by
    rw [← actRingHom_apply, map_mul, map_natCast]
    rfl
  rw [h, map_mul, natCast_smul_eq_nsmul', ← endAct_natCast]
  rfl

omit [CharP k p] in

theorem act_teich_of_mem {n : ℕ} (c : GaloisField p 2) {f : CartierModule p X.F} (hf : f ∈ piece X n) :
    endAct (X.actEnd (WittVector.teichmuller p c)) f =
      WittVector.teichmuller p (j (WittVector.teichmuller p c) ^ p ^ n) • f := by
  rw [teichmuller_smul]
  exact hf c

theorem pow_smul_eq_iterate (n : ℕ) (f : CartierModule p X.F) :
    ((p : WittVector p k) ^ n) • f = (⇑(verschiebung (p := p) (Φ := X.F)))^[n]
      ((⇑(frobenius (p := p) (Φ := X.F)))^[n] f) := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    have hcomm : Function.Commute (⇑(frobenius (p := p) (Φ := X.F)))
        (⇑(verschiebung (p := p) (Φ := X.F))) := fun g => frobenius_verschiebung g
    rw [pow_succ, mul_smul, ← verschiebung_frobenius_eq_smul, ih,
      (hcomm.iterate_left n) (frobenius f),
      ← Function.iterate_succ_apply (⇑(verschiebung (p := p) (Φ := X.F))) n,
      ← Function.iterate_succ_apply (⇑(frobenius (p := p) (Φ := X.F))) n]

theorem eq_zero_of_forall_exists_iterate (f : CartierModule p X.F)
    (hf : ∀ N : ℕ, ∃ t : CartierModule p X.F,
      f = (⇑(verschiebung (p := p) (Φ := X.F)))^[N] t) : f = 0 := by
  obtain ⟨s, -, huniq⟩ :=
    existsUnique_forall_eq_sum_range_verschiebung_iterate_add p X.F (fun _ => 0)
  have h0 : ∀ N : ℕ, ∃ t : CartierModule p X.F, (0 : CartierModule p X.F) =
      (∑ m ∈ Finset.range N, (⇑(verschiebung (p := p) (Φ := X.F)))^[m] (0 : CartierModule p X.F)) +
        (⇑(verschiebung (p := p) (Φ := X.F)))^[N] t := fun N =>
    ⟨0, by simp [iterate_map_zero]⟩
  have hf' : ∀ N : ℕ, ∃ t : CartierModule p X.F, f =
      (∑ m ∈ Finset.range N, (⇑(verschiebung (p := p) (Φ := X.F)))^[m] (0 : CartierModule p X.F)) +
        (⇑(verschiebung (p := p) (Φ := X.F)))^[N] t := fun N => by
    obtain ⟨t, ht⟩ := hf N
    exact ⟨t, by simpa [iterate_map_zero] using ht⟩
  rw [huniq f hf', ← huniq 0 h0]

theorem eq_zero_of_forall_pow_smul (f : CartierModule p X.F)
    (hf : ∀ N : ℕ, ∃ y : CartierModule p X.F, f = ((p : WittVector p k) ^ N) • y) : f = 0 := by
  refine eq_zero_of_forall_exists_iterate X f fun N => ?_
  obtain ⟨y, hy⟩ := hf N
  exact ⟨(⇑(frobenius (p := p) (Φ := X.F)))^[N] y, by rw [hy, pow_smul_eq_iterate]⟩

theorem exists_eq_teich_add (a : Zp2 p) :
    ∃ (c : GaloisField p 2) (b : Zp2 p), a = WittVector.teichmuller p c + p * b := by
  letI : Fintype (GaloisField p 2) := Fintype.ofFinite _
  set x := a - WittVector.teichmuller p (a.coeff 0) with hx
  by_cases h0 : x = 0
  · exact ⟨a.coeff 0, 0, by rw [mul_zero, add_zero]; exact (sub_eq_zero.mp h0)⟩
  obtain ⟨m, b, hb, hxb⟩ := WittVector.exists_eq_pow_p_mul x h0
  cases m with
  | zero =>
    exfalso
    apply hb
    have hx0 : x.coeff 0 = 0 := by
      rw [hx, ← WittVector.constantCoeff_apply, map_sub, WittVector.constantCoeff_apply,
        WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero, sub_self]
    rwa [hxb, pow_zero, one_mul] at hx0
  | succ m =>
    refine ⟨a.coeff 0, (p : Zp2 p) ^ m * b, ?_⟩
    rw [← mul_assoc, ← pow_succ', ← hxb, hx, add_sub_cancel]

structure LatticeData where

  e : Fin 2 → CartierModule p X.F
  mem : ∀ r, e r ∈ piece X 0
  pi_eq : ∀ r, endAct X.varpiEnd (e r) = verschiebung (e r)
  indep : ∀ w : Fin 2 → WittVector p k, ∑ r, w r • e r = 0 → w = 0
  p_mem : ∀ f ∈ piece X 0, ∃ w : Fin 2 → WittVector p k, (p : WittVector p k) • f = ∑ r, w r • e r
  pi_mem : ∀ f ∈ piece X 1, ∃ w : Fin 2 → WittVector p k, endAct X.varpiEnd f = ∑ r, w r • e r

variable {X}
variable (D : LatticeData X)

noncomputable def sumE (w : Fin 2 → WittVector p k) : CartierModule p X.F := ∑ r, w r • D.e r

theorem sumE_def (w : Fin 2 → WittVector p k) : sumE D w = ∑ r, w r • D.e r := rfl

theorem sumE_add (w w' : Fin 2 → WittVector p k) : sumE D (w + w') = sumE D w + sumE D w' := by
  simp only [sumE, Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem sumE_zero : sumE D 0 = 0 := by
  simp [sumE]

theorem sumE_smul (c : WittVector p k) (w : Fin 2 → WittVector p k) : sumE D (c • w) = c • sumE D w := by
  simp only [sumE, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

theorem sumE_sub (w w' : Fin 2 → WittVector p k) : sumE D (w - w') = sumE D w - sumE D w' := by
  rw [sub_eq_add_neg, sumE_add, ← neg_one_smul (WittVector p k) w', sumE_smul, neg_one_smul,
    sub_eq_add_neg]

theorem sumE_injective : Function.Injective (sumE D) := by
  intro w w' h
  have h0 : sumE D (w - w') = 0 := by rw [sumE_sub, h, sub_self]
  exact sub_eq_zero.mp (D.indep _ h0)

theorem sumE_mem (w : Fin 2 → WittVector p k) : sumE D w ∈ piece X 0 :=
  Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ _ (D.mem r)

theorem pi_sumE (w : Fin 2 → WittVector p k) :
    endAct X.varpiEnd (sumE D w) = verschiebung (sumE D (fun r => WittVector.frobenius (w r))) := by
  rw [sumE_def, sumE_def, map_sum, map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [pi_smul, D.pi_eq r, smul_verschiebung]

variable [PerfectRing k p]

noncomputable def sInv (w : Fin 2 → WittVector p k) : Fin 2 → WittVector p k :=
  fun r => (WittVector.frobeniusEquiv p k).symm (w r)

theorem frobenius_sInv (w : Fin 2 → WittVector p k) (r : Fin 2) :
    WittVector.frobenius (sInv w r) = w r :=
  (WittVector.frobeniusEquiv p k).apply_symm_apply (w r)

theorem sInv_smul (c : WittVector p k) (w : Fin 2 → WittVector p k) :
    sInv (c • w) = (WittVector.frobeniusEquiv p k).symm c • sInv w := by
  funext r
  simp only [sInv, Pi.smul_apply, smul_eq_mul, map_mul]

theorem verschiebung_sumE (w : Fin 2 → WittVector p k) :
    verschiebung (sumE D w) = endAct X.varpiEnd (sumE D (sInv w)) := by
  have h : (fun r => WittVector.frobenius (sInv w r)) = w := funext (frobenius_sInv w)
  rw [pi_sumE, h]

noncomputable def c₀ (m : CartierModule p X.F) : Fin 2 → WittVector p k :=
  (D.p_mem _ (pr0_mem X m)).choose

omit [PerfectRing k p] in
theorem sumE_c₀ (m : CartierModule p X.F) : sumE D (c₀ D m) = (p : WittVector p k) • pr0 X m :=
  (D.p_mem _ (pr0_mem X m)).choose_spec.symm

noncomputable def c₁ (m : CartierModule p X.F) : Fin 2 → WittVector p k :=
  (D.pi_mem _ (pr1_mem X m)).choose

omit [PerfectRing k p] in
theorem sumE_c₁ (m : CartierModule p X.F) : sumE D (c₁ D m) = endAct X.varpiEnd (pr1 X m) :=
  (D.pi_mem _ (pr1_mem X m)).choose_spec.symm

omit [PerfectRing k p] in
theorem c₀_eq {m : CartierModule p X.F} {w : Fin 2 → WittVector p k}
    (h : sumE D w = (p : WittVector p k) • pr0 X m) : c₀ D m = w :=
  sumE_injective D (by rw [sumE_c₀, h])

omit [PerfectRing k p] in
theorem c₁_eq {m : CartierModule p X.F} {w : Fin 2 → WittVector p k}
    (h : sumE D w = endAct X.varpiEnd (pr1 X m)) : c₁ D m = w :=
  sumE_injective D (by rw [sumE_c₁, h])

omit [PerfectRing k p] in
theorem c₀_add (m m' : CartierModule p X.F) : c₀ D (m + m') = c₀ D m + c₀ D m' :=
  c₀_eq D (by rw [sumE_add, sumE_c₀, sumE_c₀, map_add, smul_add])

omit [PerfectRing k p] in
theorem c₁_add (m m' : CartierModule p X.F) : c₁ D (m + m') = c₁ D m + c₁ D m' :=
  c₁_eq D (by rw [sumE_add, sumE_c₁, sumE_c₁, map_add, map_add])

omit [PerfectRing k p] in
theorem c₀_smul (w : WittVector p k) (m : CartierModule p X.F) : c₀ D (w • m) = w • c₀ D m :=
  c₀_eq D (by rw [sumE_smul, sumE_c₀, map_smul, smul_comm])

omit [PerfectRing k p] in
theorem c₁_smul (w : WittVector p k) (m : CartierModule p X.F) : c₁ D (w • m) = w • c₁ D m :=
  c₁_eq D (by rw [sumE_smul, sumE_c₁, map_smul, pi_smul])

end OneModule

section TwoModules

variable {Φ Φ' : SpecialFormalODModule p j} (D : LatticeData Φ) (D' : LatticeData Φ')

noncomputable def ThetaFun (m : CartierModule p Φ.F) : CartierModule p Φ'.F :=
  sumE D' (c₀ D m) + endAct Φ'.varpiEnd (sumE D' (c₁ D m))

noncomputable def Theta : CartierModule p Φ.F →+ CartierModule p Φ'.F where
  toFun := ThetaFun D D'
  map_zero' := by
    have h0 : c₀ D 0 = 0 := c₀_eq D (by rw [sumE_zero, map_zero, smul_zero])
    have h1 : c₁ D 0 = 0 := c₁_eq D (by rw [sumE_zero, map_zero, map_zero])
    rw [ThetaFun, h0, h1, sumE_zero, map_zero, add_zero]
  map_add' m m' := by
    simp only [ThetaFun, c₀_add, c₁_add, sumE_add, map_add]
    abel

theorem Theta_apply (m : CartierModule p Φ.F) :
    Theta D D' m = sumE D' (c₀ D m) + endAct Φ'.varpiEnd (sumE D' (c₁ D m)) := rfl

theorem Theta_of_mem {m₀ m₁ : CartierModule p Φ.F} (h₀ : m₀ ∈ piece Φ 0) (h₁ : m₁ ∈ piece Φ 1)
    {a b : Fin 2 → WittVector p k} (ha : sumE D a = (p : WittVector p k) • m₀)
    (hb : sumE D b = endAct Φ.varpiEnd m₁) :
    Theta D D' (m₀ + m₁) = sumE D' a + endAct Φ'.varpiEnd (sumE D' b) := by
  have h0 : c₀ D (m₀ + m₁) = a := c₀_eq D (by rw [pr0_of_add Φ h₀ h₁, ha])
  have h1 : c₁ D (m₀ + m₁) = b := c₁_eq D (by rw [pr1_of_add Φ h₀ h₁, hb])
  rw [Theta_apply, h0, h1]

theorem Theta_smul (w : WittVector p k) (m : CartierModule p Φ.F) :
    Theta D D' (w • m) = w • Theta D D' m := by
  rw [Theta_apply, Theta_apply, c₀_smul, c₁_smul, sumE_smul, sumE_smul, pi_smul, smul_add]

theorem Theta_p_smul (m : CartierModule p Φ.F) :
    Theta D D' ((p : WittVector p k) • m) = (p : WittVector p k) • Theta D D' m :=
  Theta_smul D D' _ m

theorem sumE'_mem_zero (w : Fin 2 → WittVector p k) : sumE D' w ∈ piece Φ' 0 := sumE_mem D' w

theorem pi_sumE'_mem_one (w : Fin 2 → WittVector p k) :
    endAct Φ'.varpiEnd (sumE D' w) ∈ piece Φ' 1 :=
  pi_mem Φ' 0 (sumE_mem D' w)

theorem Theta_pi (m : CartierModule p Φ.F) :
    Theta D D' (endAct Φ.varpiEnd m) = endAct Φ'.varpiEnd (Theta D D' m) := by
  set a := c₀ D m
  set b := c₁ D m
  have ha : sumE D a = (p : WittVector p k) • pr0 Φ m := sumE_c₀ D m
  have hb : sumE D b = endAct Φ.varpiEnd (pr1 Φ m) := sumE_c₁ D m

  have hdec : endAct Φ.varpiEnd m = endAct Φ.varpiEnd (pr1 Φ m) + endAct Φ.varpiEnd (pr0 Φ m) := by
    conv_lhs => rw [← pr0_add_pr1 Φ m]
    rw [map_add, add_comm]
  have hpb : sumE D ((p : WittVector p k) • b) = (p : WittVector p k) • endAct Φ.varpiEnd (pr1 Φ m) := by
    rw [sumE_smul, hb]
  have hpa : sumE D a = endAct Φ.varpiEnd (endAct Φ.varpiEnd (pr0 Φ m)) := by
    rw [pi_pi, ha]
  rw [hdec, Theta_of_mem D D' (pi_mem' Φ 0 (pr1_mem Φ m)) (pi_mem Φ 0 (pr0_mem Φ m)) hpb hpa,
    Theta_apply, map_add, pi_pi, sumE_smul, add_comm]

section Semilinear

variable [PerfectRing k p]

theorem Theta_verschiebung (m : CartierModule p Φ.F) :
    Theta D D' (verschiebung m) = verschiebung (Theta D D' m) := by
  have ha : sumE D (c₀ D m) = (p : WittVector p k) • pr0 Φ m := sumE_c₀ D m
  have hb : sumE D (c₁ D m) = endAct Φ.varpiEnd (pr1 Φ m) := sumE_c₁ D m

  have hVm₁ : verschiebung (pr1 Φ m) = sumE D (sInv (c₁ D m)) := by
    apply pi_injective Φ
    rw [pi_verschiebung, ← hb, verschiebung_sumE]

  have hdec : verschiebung m = verschiebung (pr1 Φ m) + verschiebung (pr0 Φ m) := by
    conv_lhs => rw [← pr0_add_pr1 Φ m]
    rw [map_add, add_comm]

  have h1 : sumE D ((p : WittVector p k) • sInv (c₁ D m)) =
      (p : WittVector p k) • verschiebung (pr1 Φ m) := by
    rw [sumE_smul, hVm₁]

  have h2 : sumE D (sInv (c₀ D m)) = endAct Φ.varpiEnd (verschiebung (pr0 Φ m)) := by
    apply pi_injective Φ
    rw [← verschiebung_sumE, ha, pi_pi, p_smul_verschiebung]
  rw [hdec, Theta_of_mem D D' (verschiebung_mem' Φ (pr1_mem Φ m))
    ((verschiebung_mem_iff Φ 0 _).mpr (pr0_mem Φ m)) h1 h2, Theta_apply, map_add,
    ← pi_verschiebung Φ', verschiebung_sumE D' (c₀ D m), verschiebung_sumE D' (c₁ D m), pi_pi,
    sumE_smul, add_comm]

theorem Theta_frobenius (m : CartierModule p Φ.F) :
    Theta D D' (frobenius m) = frobenius (Theta D D' m) := by
  apply verschiebung_injective
  rw [← Theta_verschiebung, verschiebung_frobenius_eq_smul, Theta_p_smul,
    verschiebung_frobenius_eq_smul]

end Semilinear

theorem Theta_homothety (a : k) (m : CartierModule p Φ.F) :
    Theta D D' (homothety a m) = homothety a (Theta D D' m) := by
  rw [← teichmuller_smul, Theta_smul, teichmuller_smul]

theorem Theta_act_teich (c : GaloisField p 2) (m : CartierModule p Φ.F) :
    Theta D D' (endAct (Φ.actEnd (WittVector.teichmuller p c)) m) =
      endAct (Φ'.actEnd (WittVector.teichmuller p c)) (Theta D D' m) := by
  have ha : sumE D (c₀ D m) = (p : WittVector p k) • pr0 Φ m := sumE_c₀ D m
  have hb : sumE D (c₁ D m) = endAct Φ.varpiEnd (pr1 Φ m) := sumE_c₁ D m
  have hdec : endAct (Φ.actEnd (WittVector.teichmuller p c)) m =
      WittVector.teichmuller p (j (WittVector.teichmuller p c) ^ p ^ 0) • pr0 Φ m +
        WittVector.teichmuller p (j (WittVector.teichmuller p c) ^ p ^ 1) • pr1 Φ m := by
    conv_lhs => rw [← pr0_add_pr1 Φ m]
    rw [map_add, act_teich_of_mem Φ c (pr0_mem Φ m), act_teich_of_mem Φ c (pr1_mem Φ m)]
  have h1 : sumE D (WittVector.teichmuller p (j (WittVector.teichmuller p c) ^ p ^ 0) • c₀ D m) =
      (p : WittVector p k) •
        (WittVector.teichmuller p (j (WittVector.teichmuller p c) ^ p ^ 0) • pr0 Φ m) := by
    rw [sumE_smul, ha, smul_comm]
  have h2 : sumE D (WittVector.teichmuller p (j (WittVector.teichmuller p c) ^ p ^ 1) • c₁ D m) =
      endAct Φ.varpiEnd
        (WittVector.teichmuller p (j (WittVector.teichmuller p c) ^ p ^ 1) • pr1 Φ m) := by
    rw [sumE_smul, hb, pi_smul]
  rw [hdec, Theta_of_mem D D' (Submodule.smul_mem _ _ (pr0_mem Φ m))
    (Submodule.smul_mem _ _ (pr1_mem Φ m)) h1 h2, Theta_apply, map_add,
    act_teich_of_mem Φ' c (sumE'_mem_zero D' (c₀ D m)),
    act_teich_of_mem Φ' c (pi_sumE'_mem_one D' (c₁ D m)), sumE_smul, sumE_smul, pi_smul]

omit [CharP k p] in
theorem endAct_actEnd_add (X : SpecialFormalODModule p j) (a b : Zp2 p) (f : CartierModule p X.F) :
    endAct (X.actEnd (a + b)) f = endAct (X.actEnd a) f + endAct (X.actEnd b) f := by
  rw [← actRingHom_apply, map_add, map_add]
  rfl

noncomputable def Dev (a : Zp2 p) (m : CartierModule p Φ.F) : CartierModule p Φ'.F :=
  Theta D D' (endAct (Φ.actEnd a) m) - endAct (Φ'.actEnd a) (Theta D D' m)

theorem Dev_add (a b : Zp2 p) (m : CartierModule p Φ.F) :
    Dev D D' (a + b) m = Dev D D' a m + Dev D D' b m := by
  simp only [Dev, endAct_actEnd_add, map_add]
  abel

theorem Dev_teich (c : GaloisField p 2) (m : CartierModule p Φ.F) :
    Dev D D' (WittVector.teichmuller p c) m = 0 := by
  rw [Dev, Theta_act_teich, sub_self]

theorem Dev_p_mul (a : Zp2 p) (m : CartierModule p Φ.F) :
    Dev D D' ((p : Zp2 p) * a) m = (p : WittVector p k) • Dev D D' a m := by
  rw [Dev, Dev, act_p_mul, act_p_mul, Theta_p_smul, smul_sub]

theorem Dev_forall_pow (N : ℕ) : ∀ (a : Zp2 p) (m : CartierModule p Φ.F),
    ∃ y : CartierModule p Φ'.F, Dev D D' a m = ((p : WittVector p k) ^ N) • y := by
  induction N with
  | zero => exact fun a m => ⟨Dev D D' a m, by rw [pow_zero, one_smul]⟩
  | succ N ih =>
    intro a m
    obtain ⟨c, b, rfl⟩ := exists_eq_teich_add a
    obtain ⟨y, hy⟩ := ih b m
    refine ⟨y, ?_⟩
    rw [Dev_add, Dev_teich, zero_add, Dev_p_mul, hy, ← mul_smul, ← pow_succ']

theorem Theta_act (a : Zp2 p) (m : CartierModule p Φ.F) :
    Theta D D' (endAct (Φ.actEnd a) m) = endAct (Φ'.actEnd a) (Theta D D' m) := by
  have h : Dev D D' a m = 0 :=
    eq_zero_of_forall_pow_smul Φ' _ fun N => Dev_forall_pow D D' N a m
  exact sub_eq_zero.mp h

theorem Theta_injective : Function.Injective (Theta D D') := by
  refine (injective_iff_map_eq_zero _).mpr fun m hm => ?_
  rw [Theta_apply] at hm
  have h0 : sumE D' (c₀ D m) = 0 := by
    have h := pr0_of_add Φ' (sumE'_mem_zero D' (c₀ D m)) (pi_sumE'_mem_one D' (c₁ D m))
    rw [hm, map_zero] at h
    exact h.symm
  have h1 : endAct Φ'.varpiEnd (sumE D' (c₁ D m)) = 0 := by
    have h := pr1_of_add Φ' (sumE'_mem_zero D' (c₀ D m)) (pi_sumE'_mem_one D' (c₁ D m))
    rw [hm, map_zero] at h
    exact h.symm
  have ha : c₀ D m = 0 := sumE_injective D' (by rw [h0, sumE_zero])
  have hb : c₁ D m = 0 :=
    sumE_injective D' (by rw [sumE_zero]; exact pi_injective Φ' (by rw [h1, map_zero]))
  have hm0 : pr0 Φ m = 0 := by
    apply smul_p_injective Φ
    show (p : WittVector p k) • pr0 Φ m = (p : WittVector p k) • 0
    rw [← sumE_c₀ D, ha, sumE_zero, smul_zero]
  have hm1 : pr1 Φ m = 0 := by
    apply pi_injective Φ
    rw [← sumE_c₁ D, hb, sumE_zero, map_zero]
  rw [← pr0_add_pr1 Φ m, hm0, hm1, add_zero]

theorem Theta_cofinal (g : CartierModule p Φ'.F) :
    ∃ f : CartierModule p Φ.F, Theta D D' f = ((p : WittVector p k) ^ 3) • g := by
  obtain ⟨a₀, ha₀⟩ := D'.p_mem _ (pr0_mem Φ' g)
  obtain ⟨a₁, ha₁⟩ := D'.p_mem _ (pi_mem' Φ' 0 (pr1_mem Φ' g))
  refine ⟨(p : WittVector p k) • sumE D a₀ + endAct Φ.varpiEnd (sumE D a₁), ?_⟩
  have h1 : sumE D (((p : WittVector p k) * (p : WittVector p k)) • a₀) =
      (p : WittVector p k) • ((p : WittVector p k) • sumE D a₀) := by
    rw [sumE_smul, mul_smul]
  have h2 : sumE D ((p : WittVector p k) • a₁) =
      endAct Φ.varpiEnd (endAct Φ.varpiEnd (sumE D a₁)) := by
    rw [sumE_smul, pi_pi]
  have e0 : sumE D' a₀ = (p : WittVector p k) • pr0 Φ' g := ha₀.symm
  have e1 : sumE D' a₁ = (p : WittVector p k) • endAct Φ'.varpiEnd (pr1 Φ' g) := ha₁.symm
  rw [Theta_of_mem D D' (Submodule.smul_mem _ _ (sumE_mem D a₀)) (pi_mem Φ 0 (sumE_mem D a₁)) h1 h2,
    sumE_smul, sumE_smul, e0, e1, pi_smul, pi_smul, pi_pi]
  conv_rhs => rw [← pr0_add_pr1 Φ' g, smul_add]
  rw [← mul_smul, ← mul_smul, ← mul_smul, ← pow_three']

end TwoModules

theorem nonempty_latticeData [IsAlgClosed k] (X : SpecialFormalODModule p j) :
    Nonempty (LatticeData X) := by
  obtain ⟨e, h1, h2, h3, h4, h5⟩ :=
    SpecialFormalODModule.exists_fin_two_endAct_varpiEnd_eq_verschiebung_of_isAlgClosed p k j X
  exact ⟨⟨e, h1, h2, h3, h4, h5⟩⟩

end P2mKcBC52Module

open P2mKcBC52Module MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld in
theorem solution
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [IsAlgClosed k] [CharP k p]
    (j : CerednikDrinfeld.Zp2 p →+* k) (Φ Φ' : CerednikDrinfeld.SpecialFormalODModule p j) :
    ∃ θ : MvFormalGroup.CartierModule p Φ.F →+ MvFormalGroup.CartierModule p Φ'.F,
      Function.Injective θ ∧
      (∀ f, θ (MvFormalGroup.CartierModule.frobenius f) =
        MvFormalGroup.CartierModule.frobenius (θ f)) ∧
      (∀ f, θ (MvFormalGroup.CartierModule.verschiebung f) =
        MvFormalGroup.CartierModule.verschiebung (θ f)) ∧
      (∀ (a : k) f, θ (MvFormalGroup.CartierModule.homothety a f) =
        MvFormalGroup.CartierModule.homothety a (θ f)) ∧
      (∀ (a : CerednikDrinfeld.Zp2 p) f,
        θ (MvFormalGroup.CartierModule.endAct (Φ.actEnd a) f) =
          MvFormalGroup.CartierModule.endAct (Φ'.actEnd a) (θ f)) ∧
      (∀ f, θ (MvFormalGroup.CartierModule.endAct Φ.varpiEnd f) =
        MvFormalGroup.CartierModule.endAct Φ'.varpiEnd (θ f)) ∧
      ∃ N : ℕ, ∀ g : MvFormalGroup.CartierModule p Φ'.F,
        ∃ f : MvFormalGroup.CartierModule p Φ.F, θ f = p ^ N • g := by
  obtain ⟨D⟩ := nonempty_latticeData Φ
  obtain ⟨D'⟩ := nonempty_latticeData Φ'
  refine ⟨Theta D D', Theta_injective D D', Theta_frobenius D D', Theta_verschiebung D D',
    Theta_homothety D D', Theta_act D D', Theta_pi D D', 3, fun g => ?_⟩
  obtain ⟨f, hf⟩ := Theta_cofinal D D' g
  refine ⟨f, ?_⟩
  rw [hf, ← natCast_smul_eq_nsmul', Nat.cast_pow]

end S_CerednikDrinfeld_SpecialFormalODModule_exists_addMonoidHom_cartierModule_injective_of_isAlgClosed
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_addMonoidHom_cartierModule_injective_of_isAlgClosed (solution)
