-- Prove2me | solution 1 for ChebotarevDensity.cyclePattern_pow_coprime
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-01T14:28:11.708677+00:00
-- url     : https://prove2.me/submissions/18bcb7fc-77bd-41b0-b62c-ce1d8a3cb6e4

import Definitions.Def_ChebotarevDensity_Defs
import Definitions.Def_ChebotarevDensity_Aux

open Polynomial NumberField
open ChebotarevDensity

private lemma parts_eq_of_cycleType_eq {α : Type*} [Fintype α] [DecidableEq α]
    (a b : Equiv.Perm α) (h : a.cycleType = b.cycleType) :
    a.partition.parts = b.partition.parts := by
  rw [Equiv.Perm.parts_partition, Equiv.Perm.parts_partition, h]
  have h1 := Equiv.Perm.sum_cycleType a
  have h2 := Equiv.Perm.sum_cycleType b
  rw [h] at h1
  have : a.support.card = b.support.card := by omega
  rw [this]

private lemma list_prod_pow {α : Type*} [Fintype α] [DecidableEq α] (k : ℕ)
    (l : List (Equiv.Perm α)) (hl : l.Pairwise Equiv.Perm.Disjoint) :
    (l.map (· ^ k)).prod = l.prod ^ k := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.pairwise_cons] at hl
    rw [List.map_cons, List.prod_cons, List.prod_cons, ih hl.2]
    have hc : Commute a l.prod :=
      Commute.list_prod_right _ _ (fun b hb => (hl.1 b hb).commute)
    exact (hc.mul_pow k).symm

private lemma cycleType_pow_coprime {α : Type*} [Fintype α] [DecidableEq α]
    (τ : Equiv.Perm α) (k : ℕ) (hk : Nat.Coprime k (orderOf τ)) :
    (τ ^ k).cycleType = τ.cycleType := by
  have key : ∀ l : List (Equiv.Perm α), l.prod = τ → (∀ c ∈ l, c.IsCycle) →
      l.Pairwise Equiv.Perm.Disjoint → (τ ^ k).cycleType = τ.cycleType := by
    intro l h0 h1 h2
    have hτ := Equiv.Perm.cycleType_eq l h0 h1 h2
    have hcop : ∀ c ∈ l, Nat.Coprime k (orderOf c) := by
      intro c hc
      have hmem : c.support.card ∈ τ.cycleType := by
        rw [hτ]; exact Multiset.mem_coe.mpr (List.mem_map.mpr ⟨c, hc, rfl⟩)
      rw [(h1 c hc).orderOf]
      exact Nat.Coprime.coprime_dvd_right (Equiv.Perm.dvd_of_mem_cycleType hmem) hk
    have h1' : ∀ c ∈ l.map (· ^ k), c.IsCycle := by
      intro c hc
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
      exact ((h1 d hd).pow_iff (n := k)).mpr (hcop d hd)
    have h2' : (l.map (· ^ k)).Pairwise Equiv.Perm.Disjoint := by
      rw [List.pairwise_map]
      refine h2.imp ?_
      intro a b hab x
      rcases hab x with h | h
      · left; exact Equiv.Perm.pow_apply_eq_self_of_apply_eq_self h k
      · right; exact Equiv.Perm.pow_apply_eq_self_of_apply_eq_self h k
    have hprod : (l.map (· ^ k)).prod = τ ^ k := by
      rw [list_prod_pow k l h2, h0]
    rw [Equiv.Perm.cycleType_eq _ hprod h1' h2', hτ]
    congr 1
    rw [List.map_map]
    refine List.map_congr_left ?_
    intro c hc
    simp only [Function.comp]
    rw [Equiv.Perm.support_pow_coprime (hcop c hc)]
  obtain ⟨l, h0, h1, h2⟩ := (Equiv.Perm.truncCycleFactors τ).out
  exact key l h0 h1 h2

theorem solution (f : ℤ[X]) (g : GalGroup f) (k : ℕ)
    (hk : Nat.Coprime k (orderOf g)) :
    cyclePattern f (g ^ k) = cyclePattern f g := by
  unfold cyclePattern
  refine parts_eq_of_cycleType_eq _ _ ?_
  rw [map_pow]
  refine cycleType_pow_coprime _ k ?_
  exact Nat.Coprime.coprime_dvd_right (orderOf_map_dvd _ _) hk

