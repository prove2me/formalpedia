-- Prove2me | solution 1 for CerednikDrinfeld.Mumford.isSchottky_of_relIndex_ne_zero_of_forall_isOfFinOrder_imp_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/7c8a5174-8349-52ea-855b-181dbbeee2b1

import Mathlib
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Mumford_isSchottky_of_relIndex_ne_zero_of_forall_isOfFinOrder_imp_eq_one

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.Mumford

namespace F0eAux

open MulAction

theorem finite_orbitQuot_of_relIndex_ne_zero {G : Type} [Group G] {X : Type} [MulAction G X]
    (Γ Γ'' : Subgroup G) (_hle : Γ'' ≤ Γ) (hidx : Γ''.relIndex Γ ≠ 0)
    [Finite (orbitRel.Quotient ↥Γ X)] : Finite (orbitRel.Quotient ↥Γ'' X) := by
  classical
  haveI : (Γ''.subgroupOf Γ).FiniteIndex := ⟨hidx⟩
  haveI : Finite (↥Γ ⧸ Γ''.subgroupOf Γ) := Subgroup.finite_quotient_of_finiteIndex
  let f : (↥Γ ⧸ Γ''.subgroupOf Γ) × orbitRel.Quotient ↥Γ X → orbitRel.Quotient ↥Γ'' X :=
    fun p => Quotient.mk (orbitRel ↥Γ'' X) ((p.1.out)⁻¹ • p.2.out)
  refine Finite.of_surjective f ?_
  intro o
  induction o using Quotient.inductionOn with
  | h x =>
    set oΓ : orbitRel.Quotient ↥Γ X := Quotient.mk (orbitRel ↥Γ X) x with hoΓ
    have hx₀ : (orbitRel ↥Γ X) oΓ.out x := Quotient.mk_out x
    obtain ⟨γ, hγ⟩ := (orbitRel_apply.mp hx₀ : oΓ.out ∈ orbit ↥Γ x)
    have hxγ : x = γ⁻¹ • oΓ.out := by rw [← hγ, inv_smul_smul]
    set q : ↥Γ ⧸ Γ''.subgroupOf Γ := QuotientGroup.mk γ with hq
    refine ⟨(q, oΓ), ?_⟩
    show Quotient.mk (orbitRel ↥Γ'' X) ((q.out)⁻¹ • oΓ.out) = Quotient.mk (orbitRel ↥Γ'' X) x
    apply Quotient.sound
    have hmem : γ⁻¹ * q.out ∈ Γ''.subgroupOf Γ := by
      rw [← QuotientGroup.eq]; exact (QuotientGroup.out_eq' q).symm ▸ rfl
    show (q.out)⁻¹ • oΓ.out ∈ orbit (↥Γ'') x
    rw [mem_orbit_iff]
    have hmem' : ((q.out : ↥Γ) : G)⁻¹ * (γ : G) ∈ Γ'' := by
      have := Γ''.inv_mem (Subgroup.mem_subgroupOf.mp hmem)
      simpa using this
    refine ⟨⟨_, hmem'⟩, ?_⟩
    rw [Subgroup.mk_smul, hxγ, Subgroup.smul_def, Subgroup.smul_def, Subgroup.coe_inv, Subgroup.coe_inv, mul_smul,
      smul_inv_smul]

theorem coe_eq_one_of_pow_mem_finite {H : Type} [Group H] (A : Subgroup H) (F : Subgroup ↥A) [Finite ↥F]
    (T : Subgroup H) (hT : ∀ g ∈ T, IsOfFinOrder g → g = 1)
    {x : ↥A} (hxT : (x : H) ∈ T) {n : ℕ} (hn : n ≠ 0) (hxn : x ^ n ∈ F) : (x : H) = 1 := by
  have h1 : IsOfFinOrder (⟨x ^ n, hxn⟩ : ↥F) := isOfFinOrder_of_finite _
  obtain ⟨m, hm, hm1⟩ := isOfFinOrder_iff_pow_eq_one.mp h1
  have h2 : ((x : H) ^ n) ^ m = 1 := by
    have := congrArg (fun y : ↥F => ((y : ↥A) : H)) hm1
    simpa using this
  have h3 : IsOfFinOrder ((x : H) ^ n) := isOfFinOrder_iff_pow_eq_one.mpr ⟨m, hm, h2⟩
  exact hT _ hxT (IsOfFinOrder.of_pow h3 hn)

end F0eAux

open MulAction in
theorem solution
    {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
    (h𝒯 : 𝒯.IsTree)
    (Γ : Subgroup G)
    (hstab : ∀ w : W, Finite (MulAction.stabilizer (↥Γ) w))
    (hV : Finite (QuotVert (↥Γ) W)) (hE : Finite (QuotEdge (↥Γ) 𝒯))
    (hinv : ∀ g ∈ Γ, ∀ d : 𝒯.Dart, g • d ≠ d.symm)
    (N : Subgroup G) (hle : N ≤ Γ) (hidx : N.relIndex Γ ≠ 0)
    (htf : ∀ g ∈ N, IsOfFinOrder g → g = 1) :
    IsSchottky (↥N) 𝒯 := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    intro w
    rw [Subgroup.eq_bot_iff_forall]
    intro g hg
    rw [mem_stabilizer_iff] at hg
    let x : ↥Γ := ⟨(g : G), hle g.2⟩
    have hx : x ∈ stabilizer (↥Γ) w := by
      rw [mem_stabilizer_iff]
      exact hg
    haveI := hstab w
    have h1 : (x : G) = 1 :=
      F0eAux.coe_eq_one_of_pow_mem_finite Γ (stabilizer (↥Γ) w) N htf g.2 one_ne_zero (by rw [pow_one]; exact hx)
    exact Subtype.ext h1
  ·
    intro g d h
    exact hinv (g : G) (hle g.2) d h
  ·
    haveI : Finite (orbitRel.Quotient (↥Γ) W) := hV
    exact F0eAux.finite_orbitQuot_of_relIndex_ne_zero Γ N hle hidx
  ·
    haveI : Finite (orbitRel.Quotient (↥Γ) 𝒯.Dart) := hE
    exact F0eAux.finite_orbitQuot_of_relIndex_ne_zero Γ N hle hidx

end S_CerednikDrinfeld_Mumford_isSchottky_of_relIndex_ne_zero_of_forall_isOfFinOrder_imp_eq_one
end P2MW
export P2MW.S_CerednikDrinfeld_Mumford_isSchottky_of_relIndex_ne_zero_of_forall_isOfFinOrder_imp_eq_one (solution)
