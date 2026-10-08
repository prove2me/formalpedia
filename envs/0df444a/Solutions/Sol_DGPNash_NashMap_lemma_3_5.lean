-- Prove2me | solution 1 for DGPNash.NashMap.lemma_3_5
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T07:16:54.640244+00:00
-- url     : https://prove2.me/submissions/44a6a3a9-2c1e-43cd-9bb2-ba95168a173a

import Mathlib
import Definitions.Def_DGPNash_NashMap_nashMap

set_option autoImplicit false

universe u v

namespace DGPNash.NashMap.L35Aux

open Finset

theorem prod_update_split {ι : Type*} [Fintype ι] [DecidableEq ι] {β : ι → Type*}
    (τ : ∀ i, β i) (q : ι) (c : β q) (G : ∀ i, β i → ℝ) :
    ∏ i, G i (Function.update τ q c i) = G q c * ∏ i ∈ univ.erase q, G i (τ i) := by
  rw [← Finset.mul_prod_erase univ _ (mem_univ q)]
  simp only [Function.update_self]
  congr 1
  apply prod_congr rfl
  intro i hi
  rw [Function.update_of_ne (ne_of_mem_erase hi)]

theorem single {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*} [∀ i, Fintype (S i)]
    (σ : ∀ i, S i → ℝ) (hσ : ∀ i, AGT.IsLottery (σ i)) (q : ι) (a b : S q → ℝ)
    (g : (∀ i, S i) → ℝ) (M : ℝ) (hg : ∀ s, |g s| ≤ M) :
    |∑ s, AGT.profileProb (Function.update σ q a) s * g s -
      ∑ s, AGT.profileProb (Function.update σ q b) s * g s| ≤ M * ∑ k, |a k - b k| := by
  rw [← Finset.sum_sub_distrib]
  have hP : ∀ (c : S q → ℝ) (s : ∀ i, S i), AGT.profileProb (Function.update σ q c) s =
      c (s q) * ∏ i ∈ univ.erase q, σ i (s i) := by
    intro c s
    unfold AGT.profileProb
    exact prod_update_split σ q c (fun i f => f (s i))
  have hR : ∀ s : ∀ i, S i, 0 ≤ ∏ i ∈ univ.erase q, σ i (s i) :=
    fun s => prod_nonneg fun i _ => (hσ i).1 _
  calc |∑ s, (AGT.profileProb (Function.update σ q a) s * g s -
          AGT.profileProb (Function.update σ q b) s * g s)|
        ≤ ∑ s, |AGT.profileProb (Function.update σ q a) s * g s -
          AGT.profileProb (Function.update σ q b) s * g s| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s : ∀ i, S i, (|a (s q) - b (s q)| * ∏ i ∈ univ.erase q, σ i (s i)) * M := by
        apply sum_le_sum
        intro s _
        rw [hP, hP]
        rw [show a (s q) * (∏ i ∈ univ.erase q, σ i (s i)) * g s -
            b (s q) * (∏ i ∈ univ.erase q, σ i (s i)) * g s =
            (a (s q) - b (s q)) * (∏ i ∈ univ.erase q, σ i (s i)) * g s by ring]
        rw [abs_mul, abs_mul, abs_of_nonneg (hR s)]
        exact mul_le_mul_of_nonneg_left (hg s) (mul_nonneg (abs_nonneg _) (hR s))
    _ = M * ∑ s : ∀ i, S i, ∏ i, (Function.update σ q (fun k => |a k - b k|)) i (s i) := by
        rw [Finset.mul_sum]
        apply sum_congr rfl
        intro s _
        rw [prod_update_split σ q (fun k => |a k - b k|) (fun i f => f (s i))]
        ring
    _ = M * ∑ k, |a k - b k| := by
        congr 1
        rw [← Fintype.prod_sum]
        rw [prod_update_split σ q (fun k => |a k - b k|) (fun i f => ∑ k, f k)]
        rw [Finset.prod_eq_one (fun i _ => (hσ i).2), mul_one]

theorem hybrid {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*} [∀ i, Fintype (S i)]
    (y y' : ∀ i, S i → ℝ) (hy : ∀ i, AGT.IsLottery (y i)) (hy' : ∀ i, AGT.IsLottery (y' i))
    (g : (∀ i, S i) → ℝ) (M : ℝ) (hg : ∀ s, |g s| ≤ M) :
    |∑ s, AGT.profileProb y s * g s - ∑ s, AGT.profileProb y' s * g s| ≤
      M * ∑ i, ∑ k, |y i k - y' i k| := by
  have key : ∀ T : Finset ι,
      |∑ s, AGT.profileProb y s * g s -
        ∑ s, AGT.profileProb (fun i => if i ∈ T then y' i else y i) s * g s| ≤
      M * ∑ i ∈ T, ∑ k, |y i k - y' i k| := by
    intro T
    induction T using Finset.induction_on with
    | empty => simp
    | insert t T ht ih =>
      have hσ : ∀ i, AGT.IsLottery ((fun i => if i ∈ T then y' i else y i) i) := by
        intro i
        by_cases h : i ∈ T
        · simp only [h, if_true]; exact hy' i
        · simp only [h, if_false]; exact hy i
      have e1 : (fun i => if i ∈ T then y' i else y i) =
          Function.update (fun i => if i ∈ T then y' i else y i) t (y t) := by
        funext i
        by_cases h : i = t
        · subst h; simp [ht]
        · rw [Function.update_of_ne h]
      have e2 : (fun i => if i ∈ insert t T then y' i else y i) =
          Function.update (fun i => if i ∈ T then y' i else y i) t (y' t) := by
        funext i
        by_cases h : i = t
        · subst h; simp
        · rw [Function.update_of_ne h]; simp [h]
      have hs := single _ hσ t (y t) (y' t) g M hg
      rw [← e1] at hs
      rw [e2, sum_insert ht, mul_add]
      calc _ ≤ _ := abs_sub_le _
            (∑ s, AGT.profileProb (fun i => if i ∈ T then y' i else y i) s * g s) _
        _ ≤ M * ∑ i ∈ T, ∑ k, |y i k - y' i k| + M * ∑ k, |y t k - y' t k| := add_le_add ih hs
        _ = _ := by ring
  simpa using key univ

theorem conv {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*} [∀ i, Fintype (S i)]
    [∀ i, DecidableEq (S i)] (σ : ∀ i, S i → ℝ) (p : ι) (j : S p)
    (hσ : σ p = fun k => if k = j then 1 else 0) (f : (∀ i, S i) → ℝ) :
    ∑ s, AGT.profileProb σ s * f s = ∑ s, AGT.profileProb σ s * f (Function.update s p j) := by
  apply sum_congr rfl
  intro s _
  by_cases h : s p = j
  · rw [← h, Function.update_eq_self]
  · have : AGT.profileProb σ s = 0 := by
      unfold AGT.profileProb
      exact Finset.prod_eq_zero (mem_univ p) (by rw [hσ]; simp [h])
    rw [this, zero_mul, zero_mul]

end DGPNash.NashMap.L35Aux

open Finset in
open DGPNash.NashMap in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    [∀ i, Nonempty (S i)] (hr : 2 ≤ Fintype.card ι)
    (u : ι → (∀ i, S i) → ℝ) (hu : ∀ p s, 0 ≤ u p s)
    (x x' : ∀ i, S i → ℝ)
    (hx : AGT.IsMixedProfile x) (hx' : AGT.IsMixedProfile x')
    (p : ι) (j : S p) :
    |purePayoff u x p j - purePayoff u x' p j| ≤
      maxPurePayoff u p j *
        ∑ q : ι, if q = p then 0 else ∑ i : S q, |x q i - x' q i| := by
  have hδ : AGT.IsLottery (fun k : S p => if k = j then (1 : ℝ) else 0) := by
    refine ⟨fun k => by dsimp only; split_ifs <;> norm_num, by simp⟩
  have hL : ∀ z : ∀ i, S i → ℝ, AGT.IsMixedProfile z → ∀ i,
      AGT.IsLottery (Function.update z p (fun k : S p => if k = j then (1 : ℝ) else 0) i) := by
    intro z hz i
    by_cases h : i = p
    · subst h; simpa using hδ
    · rw [Function.update_of_ne h]; exact hz i
  have hg : ∀ s : ∀ i, S i, |u p (Function.update s p j)| ≤ maxPurePayoff u p j := by
    intro s
    rw [abs_of_nonneg (hu _ _)]
    exact le_csSup (Set.finite_range _).bddAbove ⟨s, rfl⟩
  unfold purePayoff AGT.expectedPayoff
  rw [DGPNash.NashMap.L35Aux.conv _ p j (Function.update_self _ _ _) (u p),
    DGPNash.NashMap.L35Aux.conv _ p j (Function.update_self _ _ _) (u p)]
  refine (DGPNash.NashMap.L35Aux.hybrid _ _ (hL x hx) (hL x' hx') _ _ hg).trans (le_of_eq ?_)
  congr 1
  apply sum_congr rfl
  intro q _
  by_cases h : q = p
  · subst h; simp
  · rw [if_neg h, Function.update_of_ne h, Function.update_of_ne h]
