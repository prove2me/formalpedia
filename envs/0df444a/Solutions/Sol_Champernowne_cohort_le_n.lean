-- Prove2me | solution 1 for Champernowne.cohort_le_n
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:40:41.697779+00:00
-- url     : https://prove2.me/submissions/aae762b2-e577-49f6-8b0c-7c947d455cfb

module
public import Definitions.Def_LeanPool_Champernowne_Positions
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.SpecificLimits.Basic
public import Definitions.Def_LeanPool_Champernowne_Asymptotics
public import Theorems.Thm_Champernowne_pow_champM_le
public import Theorems.Thm_Champernowne_length_champBlocks
public import Theorems.Thm_Champernowne_length_champBlocks_champIndex_le
public import Theorems.Thm_Champernowne_sum_Ico_one_pow
public import Theorems.Thm_Champernowne_sum_length_cohort


set_option autoImplicit true
@[expose] public section
public section
open Champernowne
open Filter Asymptotics Topology
namespace Champernowne
theorem _root_.solution {b : ℕ} (hb : 1 < b) (n : ℕ) :
    (b - 1) * b ^ (champM b n - 2) * (champM b n - 1) ≤ n := by
  rcases Nat.lt_or_ge (champM b n) 2 with h2 | h2
  · rw [show champM b n - 1 = 0 by omega, Nat.mul_zero]
    exact Nat.zero_le n
  · have hN1 := pow_champM_le b n
    have hlen := length_champBlocks_champIndex_le b n
    rw [length_champBlocks] at hlen
    have hsub : Finset.Ico 1 (b ^ (champM b n - 1))
        ⊆ Finset.Ico 1 (champIndex b n + 1) :=
      Finset.Ico_subset_Ico_right hN1
    have hmono := Finset.sum_le_sum_of_subset
      (f := fun k => (bigDigits b k).length) hsub
    rw [sum_Ico_one_pow hb] at hmono
    have hsingle : (∑ k ∈ Finset.Ico (b ^ (champM b n - 1 - 1))
          (b ^ (champM b n - 1)), (bigDigits b k).length)
        ≤ ∑ m ∈ Finset.Icc 1 (champM b n - 1),
            ∑ k ∈ Finset.Ico (b ^ (m - 1)) (b ^ m),
              (bigDigits b k).length :=
      Finset.single_le_sum
        (f := fun m => ∑ k ∈ Finset.Ico (b ^ (m - 1)) (b ^ m),
          (bigDigits b k).length)
        (fun _ _ => Nat.zero_le _)
        (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)
    rw [sum_length_cohort hb (champM b n - 1) (by omega),
      show champM b n - 1 - 1 = champM b n - 2 by omega] at hsingle
    omega
end Champernowne
