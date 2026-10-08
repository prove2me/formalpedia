-- Prove2me | solution 1 for DGPNash.WellSupported.lemma4_26_payoff_diff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T13:08:35.606122+00:00
-- url     : https://prove2.me/submissions/94aed566-7a6a-404b-aaac-867c5f83b170

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_DGPNash_WellSupported_Equilibria

set_option autoImplicit false

namespace D4bc74a2Aux

open Finset

theorem hyb {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (a b : ∀ i, S i → ℝ) (ha : AGT.IsMixedProfile a) (hb : AGT.IsMixedProfile b)
    (T : Finset ι) :
    ∑ s : (∀ i, S i), |∏ i, (if i ∈ T then a i (s i) else b i (s i)) - ∏ i, b i (s i)| ≤
      ∑ i ∈ T, ∑ k, |a i k - b i k| := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert t T htT ih =>
    have key : ∀ s : (∀ i, S i),
        ∏ i, (if i ∈ insert t T then a i (s i) else b i (s i)) -
          ∏ i, (if i ∈ T then a i (s i) else b i (s i)) =
        ∏ i, (if i = t then a i (s i) - b i (s i)
          else if i ∈ T then a i (s i) else b i (s i)) := by
      intro s
      rw [← Finset.mul_prod_erase univ _ (mem_univ t), ← Finset.mul_prod_erase univ _ (mem_univ t),
        ← Finset.mul_prod_erase univ _ (mem_univ t)]
      have h1 : ∏ x ∈ univ.erase t, (if x ∈ insert t T then a x (s x) else b x (s x)) =
          ∏ x ∈ univ.erase t, (if x ∈ T then a x (s x) else b x (s x)) := by
        apply Finset.prod_congr rfl
        intro x hx
        have hxt : x ≠ t := Finset.ne_of_mem_erase hx
        simp [Finset.mem_insert, hxt]
      have h2 : ∏ x ∈ univ.erase t, (if x = t then a x (s x) - b x (s x)
          else if x ∈ T then a x (s x) else b x (s x)) =
          ∏ x ∈ univ.erase t, (if x ∈ T then a x (s x) else b x (s x)) := by
        apply Finset.prod_congr rfl
        intro x hx
        have hxt : x ≠ t := Finset.ne_of_mem_erase hx
        simp [hxt]
      rw [h1, h2]
      simp [htT]
      ring
    have hsplit : ∀ s : (∀ i, S i),
        |∏ i, (if i ∈ insert t T then a i (s i) else b i (s i)) - ∏ i, b i (s i)| ≤
          |∏ i, (if i = t then a i (s i) - b i (s i)
            else if i ∈ T then a i (s i) else b i (s i))| +
          |∏ i, (if i ∈ T then a i (s i) else b i (s i)) - ∏ i, b i (s i)| := by
      intro s
      rw [← key s]
      exact abs_sub_le _ _ _
    have hfirst : ∑ s : (∀ i, S i), |∏ i, (if i = t then a i (s i) - b i (s i)
            else if i ∈ T then a i (s i) else b i (s i))| = ∑ k, |a t k - b t k| := by
      simp_rw [Finset.abs_prod]
      rw [← Fintype.prod_sum (fun i k => |if i = t then a i k - b i k
            else if i ∈ T then a i k else b i k|)]
      rw [Finset.prod_eq_single t]
      · simp
      · intro i _ hit
        simp only [hit, if_false]
        by_cases hiT : i ∈ T
        · simp only [hiT, if_true]
          rw [← (ha i).2]
          exact Finset.sum_congr rfl (fun k _ => abs_of_nonneg ((ha i).1 k))
        · simp only [hiT, if_false]
          rw [← (hb i).2]
          exact Finset.sum_congr rfl (fun k _ => abs_of_nonneg ((hb i).1 k))
      · intro h; exact absurd (mem_univ t) h
    rw [Finset.sum_insert htT]
    calc _ ≤ ∑ s : (∀ i, S i), (|∏ i, (if i = t then a i (s i) - b i (s i)
            else if i ∈ T then a i (s i) else b i (s i))| +
          |∏ i, (if i ∈ T then a i (s i) else b i (s i)) - ∏ i, b i (s i)|) :=
          Finset.sum_le_sum (fun s _ => hsplit s)
      _ ≤ _ := by
          rw [Finset.sum_add_distrib, hfirst]
          linarith [ih]

theorem l1prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (a b : ∀ i, S i → ℝ) (ha : AGT.IsMixedProfile a) (hb : AGT.IsMixedProfile b) :
    ∑ s : (∀ i, S i), |∏ i, a i (s i) - ∏ i, b i (s i)| ≤ ∑ i, ∑ k, |a i k - b i k| := by
  have := hyb a b ha hb univ
  simpa using this

theorem upd_mixed {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (x : ∀ i, S i → ℝ) (hx : AGT.IsMixedProfile x) (p : ι) (j : S p) :
    AGT.IsMixedProfile (Function.update x p (fun k => if k = j then 1 else 0)) := by
  intro i
  by_cases h : i = p
  · subst h
    simp only [Function.update_self]
    refine ⟨fun k => ?_, ?_⟩
    · dsimp only
      split_ifs <;> norm_num
    · simp
  · rw [Function.update_of_ne h]
    exact hx i

end D4bc74a2Aux

open Finset in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (u : ι → (∀ i, S i) → ℝ) (hu : ∀ p s, 0 ≤ u p s) (hr : 2 ≤ Fintype.card ι)
    (x y : ∀ i, S i → ℝ) (hx : AGT.IsMixedProfile x) (hy : AGT.IsMixedProfile y)
    (p : ι) (j : S p) :
    |DGPNash.NashMap.purePayoff u x p j - DGPNash.NashMap.purePayoff u y p j| ≤
      (⨆ s : (∀ i, S i), u p (Function.update s p j)) *
        ∑ q ∈ Finset.univ.erase p, ∑ i : S q, |x q i - y q i| := by
  set δ : S p → ℝ := fun k => if k = j then 1 else 0 with hδ
  set a := Function.update x p δ with ha_def
  set b := Function.update y p δ with hb_def
  have ha : AGT.IsMixedProfile a := D4bc74a2Aux.upd_mixed x hx p j
  have hb : AGT.IsMixedProfile b := D4bc74a2Aux.upd_mixed y hy p j
  set M := ⨆ s : (∀ i, S i), u p (Function.update s p j) with hM
  have hbdd : BddAbove (Set.range (fun s : (∀ i, S i) => u p (Function.update s p j))) :=
    Set.finite_range _ |>.bddAbove
  -- nonempty profile
  have hne : ∀ i, Nonempty (S i) := by
    intro i
    obtain ⟨k, -, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := univ) (f := x i)
      (by rw [(hx i).2]; norm_num)
    exact ⟨k⟩
  have hM0 : 0 ≤ M := by
    let s0 : ∀ i, S i := fun i => Classical.choice (hne i)
    exact le_trans (hu p _) (le_ciSup hbdd s0)
  have hdiff : DGPNash.NashMap.purePayoff u x p j - DGPNash.NashMap.purePayoff u y p j =
      ∑ s : (∀ i, S i), (∏ i, a i (s i) - ∏ i, b i (s i)) * u p s := by
    simp only [DGPNash.NashMap.purePayoff, AGT.expectedPayoff, AGT.profileProb]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun s _ => by ring)
  have hterm : ∀ s : (∀ i, S i), |(∏ i, a i (s i) - ∏ i, b i (s i)) * u p s| ≤
      |∏ i, a i (s i) - ∏ i, b i (s i)| * M := by
    intro s
    rw [abs_mul, abs_of_nonneg (hu p s)]
    by_cases hs : s p = j
    · apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      have : Function.update s p j = s := by rw [← hs]; exact Function.update_eq_self p s
      calc u p s = u p (Function.update s p j) := by rw [this]
        _ ≤ M := le_ciSup hbdd s
    · have h1 : ∏ i, a i (s i) = 0 :=
        Finset.prod_eq_zero (mem_univ p) (by simp [ha_def, hδ, hs])
      have h2 : ∏ i, b i (s i) = 0 :=
        Finset.prod_eq_zero (mem_univ p) (by simp [hb_def, hδ, hs])
      simp [h1, h2]
  have hsum : ∑ i, ∑ k, |a i k - b i k| =
      ∑ q ∈ Finset.univ.erase p, ∑ i : S q, |x q i - y q i| := by
    rw [← Finset.add_sum_erase univ _ (mem_univ p)]
    have hp0 : ∑ k, |a p k - b p k| = 0 := by simp [ha_def, hb_def]
    rw [hp0, zero_add]
    apply Finset.sum_congr rfl
    intro q hq
    have hqp : q ≠ p := Finset.ne_of_mem_erase hq
    simp [ha_def, hb_def, Function.update_of_ne hqp]
  rw [hdiff]
  calc _ ≤ ∑ s : (∀ i, S i), |(∏ i, a i (s i) - ∏ i, b i (s i)) * u p s| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s : (∀ i, S i), |∏ i, a i (s i) - ∏ i, b i (s i)| * M :=
        Finset.sum_le_sum (fun s _ => hterm s)
    _ = (∑ s : (∀ i, S i), |∏ i, a i (s i) - ∏ i, b i (s i)|) * M := by
        rw [Finset.sum_mul]
    _ ≤ (∑ i, ∑ k, |a i k - b i k|) * M :=
        mul_le_mul_of_nonneg_right (D4bc74a2Aux.l1prod a b ha hb) hM0
    _ = _ := by rw [hsum, mul_comm]
