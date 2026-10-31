-- Prove2me | solution 1 for BudgetFeasSubmod.Main.lemma_2_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T19:38:36.518805+00:00
-- url     : https://prove2.me/submissions/1c9897f0-9a61-460f-8c47-4b07057f2070

import Mathlib
import Definitions.Def_BudgetFeasSubmod_Main_Model

open BudgetFeasSubmod.Main

theorem solution {A : Type} [Fintype A] [DecidableEq A] (f : (A → ℝ) → Finset A) (B : ℝ)
    (hB : 0 < B) (hf : IsMonotoneRule f B) :
    IsTruthful f B ∧ IsIR f B := by
  -- the set of bids `t ∈ [s, B]` with which `i` wins, all other bids fixed by `c`
  have bdd : ∀ (c : A → ℝ) (i : A) (s : ℝ),
      BddAbove {t : ℝ | t ∈ Set.Icc s B ∧ i ∈ f (Function.update c i t)} :=
    fun c i s => ⟨B, fun t ht => ht.1.2⟩
  have mem : ∀ (c : A → ℝ) (i : A) (s : ℝ), s ≤ B → i ∈ f (Function.update c i s) →
      s ∈ {t : ℝ | t ∈ Set.Icc s B ∧ i ∈ f (Function.update c i t)} :=
    fun c i s hs h => ⟨⟨le_refl s, hs⟩, h⟩
  -- the threshold does not depend on the winning bid
  have same : ∀ (c : A → ℝ) (i : A) (s u : ℝ), s ≤ B → u ≤ B →
      i ∈ f (Function.update c i s) → i ∈ f (Function.update c i u) →
      sSup {t : ℝ | t ∈ Set.Icc s B ∧ i ∈ f (Function.update c i t)} ≤
        sSup {t : ℝ | t ∈ Set.Icc u B ∧ i ∈ f (Function.update c i t)} := by
    intro c i s u hs hu h1 h2
    apply csSup_le ⟨s, mem c i s hs h1⟩
    intro t ht
    by_cases htu : u ≤ t
    · exact le_csSup (bdd c i u) ⟨⟨htu, ht.1.2⟩, ht.2⟩
    · exact le_trans (le_of_lt (lt_of_not_ge htu)) (le_csSup (bdd c i u) (mem c i u hu h2))
  have thr_eq : ∀ (c : A → ℝ) (i : A) (s : ℝ), thr f B (Function.update c i s) i =
      if i ∈ f (Function.update c i s) then
        sSup {t : ℝ | t ∈ Set.Icc s B ∧ i ∈ f (Function.update c i t)} else 0 := by
    intro c i s
    unfold thr
    simp only [Function.update_self, Function.update_idem]
  refine ⟨?_, ?_⟩
  · intro c t i hc ht0 htB
    have hci : Function.update c i (c i) = c := Function.update_eq_self i c
    unfold utility
    rw [thr_eq c i t]
    have hthr : thr f B c i = thr f B (Function.update c i (c i)) i := by rw [hci]
    rw [hthr, thr_eq c i (c i), hci]
    by_cases hw : i ∈ f c
    · have hw' : i ∈ f (Function.update c i (c i)) := by rw [hci]; exact hw
      have hge : c i ≤ sSup {t : ℝ | t ∈ Set.Icc (c i) B ∧ i ∈ f (Function.update c i t)} :=
        le_csSup (bdd c i (c i)) (mem c i (c i) (hc i).2 hw')
      by_cases ht : i ∈ f (Function.update c i t)
      · simp only [hw, ht, if_true]
        have := same c i t (c i) htB (hc i).2 ht hw'
        linarith
      · simp only [hw, ht, if_true, if_false]
        linarith
    · by_cases ht : i ∈ f (Function.update c i t)
      · simp only [hw, ht, if_true, if_false]
        have : sSup {s : ℝ | s ∈ Set.Icc t B ∧ i ∈ f (Function.update c i s)} ≤ c i := by
          apply csSup_le ⟨t, mem c i t htB ht⟩
          intro s hs
          by_contra hlt
          push Not at hlt
          apply hw
          have hdom : InDomain B (Function.update c i s) := by
            intro j
            by_cases hj : j = i
            · subst hj; simp only [Function.update_self]
              exact ⟨le_trans ht0 hs.1.1, hs.1.2⟩
            · rw [Function.update_of_ne hj]; exact hc j
          have := hf (Function.update c i s) i (c i) hdom (hc i).1
            (by simp only [Function.update_self]; exact le_of_lt hlt) hs.2
          rwa [Function.update_idem, hci] at this
        linarith
      · simp only [hw, ht, if_false]
        exact le_refl _
  · intro b hb i
    unfold thr
    by_cases hw : i ∈ f b
    · simp only [hw, if_true]
      have hmem : b i ∈ {t : ℝ | t ∈ Set.Icc (b i) B ∧ i ∈ f (Function.update b i t)} :=
        ⟨⟨le_refl _, (hb i).2⟩, by rw [Function.update_eq_self]; exact hw⟩
      have h1 := le_csSup (bdd b i (b i)) hmem
      exact ⟨le_trans (hb i).1 h1, fun _ => h1⟩
    · simp only [hw, if_false]
      simp [hw]
