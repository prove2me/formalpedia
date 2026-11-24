-- Prove2me | solution 1 for BalanceSpecification.Growth.rate_le_of_tiling_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:39:08.91658+00:00
-- url     : https://prove2.me/submissions/26784128-f656-457c-80bd-840fee56248f

module
public import Definitions.Def_BalanceSpecificaton_Growth
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_GrowthTiling
public import Theorems.Thm_BalanceSpecification_Growth_rate_le_of_tiling_bound

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Set Filter
open scoped Topology
open BalanceSpecification BalanceSpecification.Growth
namespace BalanceSpecification.Growth
theorem _root_.solution {a b : ℕ → ℝ} (ha : ∀ n, 1 ≤ a n)
    (hb : ∀ n, 1 ≤ b n) (hsa : Submultiplicative a)
    (hbound : ∀ n : ℕ, 0 < n → ∃ M : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ k : ℕ, a (2 * M + k * n) ≤ C * (b n) ^ k) :
    rate a ≤ rate b := by
  rw [rate]
  apply le_csInf
  · exact ⟨Real.log (b 1) / (1 : ℕ), 1, (by simp only [mem_Ici, le_refl]), rfl⟩
  · rintro _ ⟨n, hn, rfl⟩
    have hnpos : 0 < n := Nat.lt_of_lt_of_le Nat.zero_lt_one (Set.mem_Ici.mp hn)
    obtain ⟨M, C, hC, hbound⟩ := hbound n hnpos
    exact rate_le_of_tiling_bound ha hsa hnpos hC
      (lt_of_lt_of_le zero_lt_one (hb n)) hbound
end BalanceSpecification.Growth
