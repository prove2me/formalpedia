-- Prove2me | solution 1 for FairSelling.ZeroPrice.thr_le_pool
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:42:31.05865+00:00
-- url     : https://prove2.me/submissions/3c562d47-4902-48f4-8c1c-1e37852878c4

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefxZero
import Theorems.Thm_FairSelling_ZeroPrice_truncBundle_le_two_thr
import Theorems.Thm_FairSelling_TPS_nonneg
import Theorems.Thm_FairSelling_TPS_truncSum


set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.ZeroPrice
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
namespace FairSelling.ZeroPrice
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) (hp0 : ∀ g, p g = 0)
    (hv : ∀ i g, 0 ≤ v i g) (hn : 0 < n) (s : St G n) (hs : GoodSt v p s)
    {j : Fin n} (hj : j ∉ s.1) :
    thr v p j ≤ bval (v j) (pool s) := by
  classical
  have hp : ∀ g, 0 ≤ p g := fun g => le_of_eq (hp0 g).symm
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hden : (0:ℝ) < 2 * n - 1 := by linarith
  set t := TPS n (v j) p with ht
  have ht0 : 0 ≤ t := TPS_nonneg (v j) p hp
  have hthr : thr v p j = ((n : ℝ) / (2 * n - 1)) * t := rfl
  have hthr0 : 0 ≤ thr v p j := by
    rw [hthr]; exact mul_nonneg (div_nonneg (by linarith) (le_of_lt hden)) ht0
  have hthr_eq : (2 * (n : ℝ) - 1) * thr v p j = (n : ℝ) * t := by
    rw [hthr]; field_simp
  -- the total truncated value is `n · TPS`
  have htotal : ∑ g : G, trunc (v j) p t g = (n : ℝ) * t := by
    have hfix : truncSum n (v j) p t = t := TPS_truncSum (v j) p hp
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    unfold truncSum at hfix
    field_simp at hfix
    simpa [trunc] using hfix
  -- split the goods into the pool and the assigned bundles
  set U : Finset G := Finset.univ.biUnion s.2 with hU
  have hUsub : U ⊆ Finset.univ := Finset.subset_univ _
  have hdisj : ((Finset.univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint s.2 := by
    intro a _ b _ hab
    exact hs.2.1 a b hab
  have hsplit : ∑ g ∈ pool s, trunc (v j) p t g + ∑ g ∈ U, trunc (v j) p t g
      = ∑ g : G, trunc (v j) p t g := Finset.sum_sdiff hUsub
  have hbi : ∑ g ∈ U, trunc (v j) p t g
      = ∑ i : Fin n, ∑ g ∈ s.2 i, trunc (v j) p t g := Finset.sum_biUnion hdisj
  -- each assigned bundle costs at most `2τ`
  have hcost : ∀ i : Fin n, ∑ g ∈ s.2 i, trunc (v j) p t g
      ≤ if i ∈ s.1 then 2 * thr v p j else 0 := by
    intro i
    by_cases hi : i ∈ s.1
    · simp only [hi, if_true]
      exact truncBundle_le_two_thr v p hp0 hv hn s hs hi hj
    · simp only [hi, if_false, hs.1 i hi, Finset.sum_empty, le_refl]
  have hcostsum : ∑ i : Fin n, ∑ g ∈ s.2 i, trunc (v j) p t g
      ≤ (s.1.card : ℝ) * (2 * thr v p j) := by
    calc ∑ i : Fin n, ∑ g ∈ s.2 i, trunc (v j) p t g
        ≤ ∑ i : Fin n, if i ∈ s.1 then 2 * thr v p j else 0 :=
          Finset.sum_le_sum (fun i _ => hcost i)
      _ = (s.1.card : ℝ) * (2 * thr v p j) := by
          rw [Finset.sum_ite_mem]
          simp [Finset.sum_const]
  -- the number of served agents is at most `n - 1`
  have hcard : (s.1.card : ℝ) ≤ (n : ℝ) - 1 := by
    have h1 : s.1.card < n := by
      have : s.1 ⊂ Finset.univ := by
        refine Finset.ssubset_univ_iff.mpr (fun hcon => ?_)
        exact hj (hcon ▸ Finset.mem_univ j)
      simpa using Finset.card_lt_card this
    have : (s.1.card : ℝ) < (n : ℝ) := by exact_mod_cast h1
    have h2 : s.1.card + 1 ≤ n := h1
    have : ((s.1.card : ℝ) + 1) ≤ (n : ℝ) := by exact_mod_cast h2
    linarith
  -- the pool retains at least `τ`
  have hpoolt : thr v p j ≤ ∑ g ∈ pool s, trunc (v j) p t g := by
    have := hsplit
    rw [hbi, htotal] at this
    nlinarith [hcostsum, hcard, hthr0, hthr_eq]
  refine le_trans hpoolt (Finset.sum_le_sum (fun g _ => ?_))
  simp only [trunc, hp0 g]
  exact max_le (hv j g) (min_le_left _ _)
end FairSelling.ZeroPrice
