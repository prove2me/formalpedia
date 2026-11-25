-- Prove2me | solution 1 for Erdos393.erdos_393.variants.luca
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T16:03:02.365648+00:00
-- url     : https://prove2.me/submissions/a7014214-861b-4eb0-af31-289fab48c5ad

module
public import Mathlib
public import Definitions.Def_Erdos393Palomar_Solution
public import Theorems.Thm_Erdos393Proof_eventually_mul_pow_lt_factorial
public import Theorems.Thm_Erdos393Proof_shape_bound

set_option autoImplicit true
@[expose] public section
public section
open Filter Asymptotics
open scoped Nat
open Erdos393
open ABC
namespace Erdos393
namespace erdos_393.variants
theorem _root_.solution (habc : ∀ (ε : ℝ) (hε : 0 < ε),
    {t : ℕ × ℕ × ℕ | 0 < t.1 ∧ 0 < t.2.1 ∧ 0 < t.2.2 ∧ ({t.1, t.2.1, t.2.2} : Set ℕ).Pairwise Nat.Coprime ∧
    t.1 + t.2.1 = t.2.2 ∧ (radical <| t.1 * t.2.1 * t.2.2 : ℝ)^(1 + ε) < t.2.2}.Finite) : Tendsto f atTop atTop := by
  have habc : Erdos393Proof.AbcHyp := fun ε hε ↦ habc ε hε
  rw [tendsto_atTop]
  intro M
  have key : ∀ T ∈ (Finset.range M).powerset, ∀ᶠ n in atTop,
      0 ∈ T → ∀ m ∈ T, m ≠ 0 → ∀ a, ∏ i ∈ T, (a + i) ≠ n ! := by
    intro T _
    by_cases hT : 0 ∈ T ∧ ∃ m ∈ T, m ≠ 0
    · obtain ⟨h0, m, hm, hm0⟩ := hT
      obtain ⟨K, X, hKX⟩ := Erdos393Proof.shape_bound habc T h0 hm hm0
      filter_upwards [Erdos393Proof.eventually_mul_pow_lt_factorial K X] with n hn
      intro _ _ _ _ a ha
      exact absurd (hKX a n ha) (not_le.2 hn)
    · exact Filter.Eventually.of_forall fun n h0 m hm hm0 ↦ absurd ⟨h0, m, hm, hm0⟩ hT
  filter_upwards [(Filter.eventually_all_finset _).2 key, eventually_ge_atTop 2] with n hn hn2
  by_contra hlt
  rw [not_le] at hlt
  have hne : {m : ℕ | 1 ≤ m ∧ ∃ a : ℕ, ∃ s ⊆ Finset.Icc a (a + m), a ∈ s ∧ a + m ∈ s ∧
      ∏ i ∈ s, i = n !}.Nonempty := by
    refine ⟨n - 1, by omega, 1, Finset.Ico 1 (n + 1), ?_, ?_, ?_,
      Finset.prod_Ico_id_eq_factorial n⟩
    · intro i hi
      obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hi
      exact Finset.mem_Icc.2 ⟨h1, by omega⟩
    · exact Finset.mem_Ico.2 ⟨le_rfl, by omega⟩
    · exact Finset.mem_Ico.2 ⟨by omega, by omega⟩
  obtain ⟨hm1, a, s, hs, has, hams, hprod⟩ : f n ∈ {m : ℕ | 1 ≤ m ∧ ∃ a : ℕ,
      ∃ s ⊆ Finset.Icc a (a + m), a ∈ s ∧ a + m ∈ s ∧ ∏ i ∈ s, i = n !} := Nat.sInf_mem hne
  have hsa : ∀ x ∈ s, a ≤ x ∧ x ≤ a + f n := fun x hx ↦ Finset.mem_Icc.1 (hs hx)
  have hT : s.image (fun x ↦ x - a) ∈ (Finset.range M).powerset := by
    rw [Finset.mem_powerset]
    intro i hi
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hi
    have := hsa x hx
    rw [Finset.mem_range]
    omega
  refine hn _ hT (Finset.mem_image.2 ⟨a, has, Nat.sub_self a⟩) (f n)
    (Finset.mem_image.2 ⟨a + f n, hams, by omega⟩) (by omega) a ?_
  rw [Finset.prod_image fun x hx y hy hxy ↦ by
    have := hsa x hx
    have := hsa y hy
    omega]
  rw [← hprod]
  exact Finset.prod_congr rfl fun x hx ↦ by
    have := hsa x hx
    omega
end erdos_393.variants
end Erdos393
