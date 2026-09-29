-- Prove2me | solution 1 for CongruenceSubgroup.Gamma0_le_closure_T_union_setOf_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/8c5228fe-c9a1-5798-981d-7911de1bcddf

import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Data.ZMod.Units
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.Group
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CongruenceSubgroup_Gamma0_le_closure_T_union_setOf_dvd

set_option autoImplicit false

namespace AlliAux1Gen

theorem exists_isCoprime_add_mul (a c : ℤ) {q : ℕ} (hq : q ≠ 0) (hac : IsCoprime a c) :
    ∃ j : ℤ, IsCoprime (a + j * c) (q : ℤ) := by
  classical
  let ps : Finset ℕ := {p ∈ q.primeFactors | ¬ (p : ℤ) ∣ a}
  refine ⟨((ps.prod id : ℕ) : ℤ), ?_⟩
  set j : ℤ := ((ps.prod id : ℕ) : ℤ) with hjdef
  rw [Int.isCoprime_iff_gcd_eq_one]
  by_contra hne
  obtain ⟨p, pp, hp⟩ := Nat.exists_prime_and_dvd hne
  have hp1 : (p : ℤ) ∣ a + j * c :=
    (Int.natCast_dvd_natCast.mpr hp).trans (Int.gcd_dvd_left _ _)
  have hp2 : p ∣ q := by
    have h : (p : ℤ) ∣ (q : ℤ) := (Int.natCast_dvd_natCast.mpr hp).trans (Int.gcd_dvd_right _ _)
    exact Int.natCast_dvd_natCast.mp h
  have ppZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp pp
  by_cases hpa : (p : ℤ) ∣ a
  ·
    have hjc : (p : ℤ) ∣ j * c := by
      have := dvd_sub hp1 hpa
      rwa [add_sub_cancel_left] at this
    rcases ppZ.dvd_or_dvd hjc with h | h
    ·
      have h' : p ∣ ps.prod id := Int.natCast_dvd_natCast.mp h
      obtain ⟨r, hr, hpr⟩ := (pp.prime.dvd_finsetProd_iff id).mp h'
      have hr' := (Finset.mem_filter.mp hr)
      have hreq : p = r :=
        (Nat.prime_dvd_prime_iff_eq pp (Nat.prime_of_mem_primeFactors hr'.1)).mp hpr
      exact hr'.2 (hreq ▸ hpa)
    ·
      exact ppZ.not_unit (hac.isUnit_of_dvd' hpa h)
  ·
    have pps : p ∈ ps :=
      Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨pp, hp2, hq⟩, hpa⟩
    have hpj : (p : ℤ) ∣ j := Int.natCast_dvd_natCast.mpr (Finset.dvd_prod_of_mem id pps)
    have : (p : ℤ) ∣ a := by
      have := dvd_sub hp1 (hpj.mul_right c)
      rwa [add_sub_cancel_right] at this
    exact hpa this

open Matrix.SpecialLinearGroup in

theorem T_zpow_mul_mul_T_zpow_apply (j j' : ℤ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    ((ModularGroup.T ^ j * γ * ModularGroup.T ^ j' :
        Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 1 0
        = (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 ∧
      ((ModularGroup.T ^ j * γ * ModularGroup.T ^ j' :
        Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 0 1
        = ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 + j * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0) * j'
          + ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 + j * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) := by
  constructor <;>
  · simp [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow, Matrix.mul_apply,
      Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
    try ring

end AlliAux1Gen

theorem solution (M : ℕ) {q : ℕ} (hq : q ≠ 0) :
    CongruenceSubgroup.Gamma0 M ≤ Subgroup.closure
      ({ModularGroup.T} ∪ {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ |
        (M : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 ∧ (q : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1}) := by
  intro γ hγ
  set H := Subgroup.closure
      ({ModularGroup.T} ∪ {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ |
        (M : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 ∧ (q : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1})
    with hH
  have hT : ModularGroup.T ∈ H := Subgroup.subset_closure (Or.inl rfl)
  have hc : (M : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (CongruenceSubgroup.Gamma0_mem.mp hγ)
  obtain ⟨j, hj⟩ := AlliAux1Gen.exists_isCoprime_add_mul
    ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0) ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0) hq
    (Matrix.SpecialLinearGroup.isCoprime_col γ 0)
  obtain ⟨u, v, huv⟩ := hj
  set a₁ : ℤ := (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 + j * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 with ha₁
  set b₁ : ℤ := (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 + j * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 with hb₁
  set j' : ℤ := -(b₁ * u) with hj'
  have hmem : ModularGroup.T ^ j * γ * ModularGroup.T ^ j' ∈ H := by
    refine Subgroup.subset_closure (Or.inr ?_)
    obtain ⟨h10, h01⟩ := AlliAux1Gen.T_zpow_mul_mul_T_zpow_apply j j' γ
    refine ⟨?_, ?_⟩
    · rw [h10]; exact hc
    · rw [h01]
      refine ⟨b₁ * v, ?_⟩
      have : a₁ * j' + b₁ = b₁ * (1 - u * a₁) := by rw [hj']; ring
      rw [← ha₁, ← hb₁, this, ← huv]
      ring
  have hγeq : γ = ModularGroup.T ^ (-j) * (ModularGroup.T ^ j * γ * ModularGroup.T ^ j')
      * ModularGroup.T ^ (-j') := by group
  rw [hγeq]
  exact H.mul_mem (H.mul_mem (H.zpow_mem hT _) hmem) (H.zpow_mem hT _)

end S_CongruenceSubgroup_Gamma0_le_closure_T_union_setOf_dvd
end P2MW
export P2MW.S_CongruenceSubgroup_Gamma0_le_closure_T_union_setOf_dvd (solution)
