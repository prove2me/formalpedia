-- Prove2me | solution 1 for FairSelling.ZeroPrice.exists_better
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:44:10.686532+00:00
-- url     : https://prove2.me/submissions/154811a5-3f20-40ce-b905-5a881fb90527

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefxZero
import Theorems.Thm_FairSelling_ZeroPrice_exists_minimal_sub
import Theorems.Thm_FairSelling_ZeroPrice_thr_le_pool

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.ZeroPrice
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
namespace FairSelling.ZeroPrice
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) (hp0 : ∀ g, p g = 0)
    (hv : ∀ i g, 0 ≤ v i g) (hn : 0 < n) (s : St G n) (hs : GoodSt v p s)
    (hT : s.1 ≠ Finset.univ) :
    ∃ s' : St G n, GoodSt v p s' ∧
      (s.1.card < s'.1.card ∨
        (s'.1.card = s.1.card ∧ ∑ i, bval (v i) (s.2 i) < ∑ i, bval (v i) (s'.2 i))) := by
  classical
  obtain ⟨j, hj⟩ : ∃ j : Fin n, j ∉ s.1 := by
    by_contra hcon
    push_neg at hcon
    exact hT (Finset.eq_univ_iff_forall.mpr hcon)
  -- the pool is claimed by the unserved agent `j`
  have hclaimpool : Claimed v p s (pool s) := by
    refine ⟨j, ?_⟩
    simp only [Claims, hj, if_false]
    exact thr_le_pool v p hp0 hv hn s hs hj
  obtain ⟨C, hCsub, hCclaim, hCmin⟩ := exists_minimal_sub (Claimed v p s) (pool s) hclaimpool
  obtain ⟨k, hk⟩ := hCclaim
  -- `C` is disjoint from every assigned bundle
  have hCdisj : ∀ i, Disjoint C (s.2 i) := by
    intro i
    refine Finset.disjoint_left.mpr (fun g hgC hgi => ?_)
    have hmem := hCsub hgC
    simp only [pool, Finset.mem_sdiff, Finset.mem_biUnion] at hmem
    exact hmem.2 ⟨i, Finset.mem_univ i, hgi⟩
  -- minimality, in the form needed for safety
  have hmin : ∀ g ∈ C, ∀ m : Fin n, bval (v m) (C.erase g) ≤ theta v p s m := by
    intro g hg m
    have hnc : ¬ Claims v p s (C.erase g) m := fun hc => hCmin g hg ⟨m, hc⟩
    by_cases hms : m ∈ s.1
    · simp only [Claims, hms, if_true, not_lt] at hnc
      simpa [theta, hms] using hnc
    · simp only [Claims, hms, if_false, not_le] at hnc
      simp only [theta, hms, if_false]
      exact le_of_lt hnc
  set A' : Fin n → Finset G := Function.update s.2 k C with hA'def
  have hA'k : A' k = C := by simp [hA'def]
  have hA'ne : ∀ i, i ≠ k → A' i = s.2 i := by
    intro i hi
    simp [hA'def, Function.update_of_ne hi]
  have hdisj' : ∀ i j : Fin n, i ≠ j → Disjoint (A' i) (A' j) := by
    intro a b hab
    by_cases hak : a = k
    · subst hak
      rw [hA'k, hA'ne b (Ne.symm hab)]
      exact hCdisj b
    · by_cases hbk : b = k
      · subst hbk
        rw [hA'k, hA'ne a hak]
        exact (hCdisj a).symm
      · rw [hA'ne a hak, hA'ne b hbk]
        exact hs.2.1 a b hab
  by_cases hks : k ∈ s.1
  · -- the claimant already holds a bundle: it exchanges it for `C`
    have hgain : bval (v k) (s.2 k) < bval (v k) C := by
      simpa [Claims, hks] using hk
    have hthrk : thr v p k ≤ bval (v k) C := le_trans (hs.2.2.1 k hks) (le_of_lt hgain)
    have hthetamono : ∀ m, theta v p s m ≤ theta v p (s.1, A') m := by
      intro m
      by_cases hmk : m = k
      · subst hmk
        simp only [theta, hks, if_true, hA'k]
        exact le_of_lt hgain
      · by_cases hms : m ∈ s.1 <;> simp [theta, hms, hA'ne m hmk]
    refine ⟨(s.1, A'), ⟨?_, hdisj', ?_, ?_⟩, Or.inr ⟨rfl, ?_⟩⟩
    · intro i hi
      dsimp only at hi ⊢
      have hik : i ≠ k := fun h => hi (h ▸ hks)
      rw [hA'ne i hik]
      exact hs.1 i hi
    · intro i hi
      dsimp only at hi ⊢
      by_cases hik : i = k
      · subst hik; rw [hA'k]; exact hthrk
      · rw [hA'ne i hik]; exact hs.2.2.1 i hi
    · intro i hi m g hg
      dsimp only at hi hg ⊢
      by_cases hik : i = k
      · subst hik
        rw [hA'k] at hg ⊢
        exact le_trans (hmin g hg m) (hthetamono m)
      · rw [hA'ne i hik] at hg ⊢
        exact le_trans (hs.2.2.2 i hi m g hg) (hthetamono m)
    · have h1 : ∑ i, bval (v i) (A' i)
          = bval (v k) C + ∑ i ∈ Finset.univ.erase k, bval (v i) (s.2 i) := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k), hA'k]
        refine congrArg _ (Finset.sum_congr rfl (fun i hi => ?_))
        rw [hA'ne i (Finset.mem_erase.mp hi).1]
      have h2 : ∑ i, bval (v i) (s.2 i)
          = bval (v k) (s.2 k) + ∑ i ∈ Finset.univ.erase k, bval (v i) (s.2 i) :=
        (Finset.add_sum_erase _ _ (Finset.mem_univ k)).symm
      simp only [h1, h2]
      linarith
  · -- the claimant is unserved: it is served now
    have hthrk : thr v p k ≤ bval (v k) C := by
      simpa [Claims, hks] using hk
    have hthetamono : ∀ m, theta v p s m ≤ theta v p (insert k s.1, A') m := by
      intro m
      by_cases hmk : m = k
      · subst hmk
        simp only [theta, Finset.mem_insert, true_or, if_true, hks, if_false, hA'k]
        exact hthrk
      · by_cases hms : m ∈ s.1 <;>
          simp [theta, hms, hA'ne m hmk, Finset.mem_insert, hmk]
    refine ⟨(insert k s.1, A'), ⟨?_, hdisj', ?_, ?_⟩, Or.inl ?_⟩
    · intro i hi
      dsimp only at hi ⊢
      have hik : i ≠ k := fun h => hi (by simp [h])
      rw [hA'ne i hik]
      exact hs.1 i (fun hcon => hi (Finset.mem_insert_of_mem hcon))
    · intro i hi
      dsimp only at hi ⊢
      by_cases hik : i = k
      · subst hik; rw [hA'k]; exact hthrk
      · rw [hA'ne i hik]
        exact hs.2.2.1 i ((Finset.mem_insert.mp hi).resolve_left hik)
    · intro i hi m g hg
      dsimp only at hi hg ⊢
      by_cases hik : i = k
      · subst hik
        rw [hA'k] at hg ⊢
        exact le_trans (hmin g hg m) (hthetamono m)
      · rw [hA'ne i hik] at hg ⊢
        exact le_trans
          (hs.2.2.2 i ((Finset.mem_insert.mp hi).resolve_left hik) m g hg) (hthetamono m)
    · simpa using Finset.card_lt_card (Finset.ssubset_insert hks)
end FairSelling.ZeroPrice
