-- Prove2me | solution 1 for EdmondsKarp.ShortestPath.bottleneck_count_le
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T19:49:52.97041+00:00
-- url     : https://prove2.me/submissions/0aadacb5-10b1-49cb-a362-616963ab874f

import Theorems.Thm_EdmondsKarp_ShortestPath_resDist_monotone
import Theorems.Thm_EdmondsKarp_ShortestPath_resDist_add_two_of_reversed
import Theorems.Thm_EdmondsKarp_ShortestPath_bottleneck_twice_reversed_between

open EdmondsKarp.ShortestPath

private theorem local_card_le_of_gap_two (S : Finset ℕ) (d : ℕ → ℕ) (n : ℕ)
    (hbound : ∀ k ∈ S, d k < n)
    (hgap : ∀ k ∈ S, ∀ l ∈ S, k < l → d k + 2 ≤ d l) :
    2 * S.card ≤ n + 1 := by
  have hind : ∀ i (hi : i < S.card), 2 * i ≤ d (S.orderEmbOfFin rfl ⟨i, hi⟩) := by
    intro i
    induction i with
    | zero => intro hi; omega
    | succ i ih =>
      intro hi
      have hi' : i < S.card := by omega
      have hp := ih hi'
      have hg := hgap _ (S.orderEmbOfFin_mem rfl ⟨i, hi'⟩)
        _ (S.orderEmbOfFin_mem rfl ⟨i + 1, hi⟩)
        ((S.orderEmbOfFin rfl).strictMono (show (⟨i, hi'⟩ : Fin S.card) < ⟨i + 1, hi⟩ from Nat.lt_succ_self i))
      omega
  by_cases hz : S.card = 0
  · simp [hz]
  · have hi : S.card - 1 < S.card := by omega
    have hp := hind (S.card - 1) hi
    have hb := hbound _ (S.orderEmbOfFin_mem rfl ⟨S.card - 1, hi⟩)
    omega

private theorem local_resDist_monotone_run {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (K : ℕ) (f : ℕ → V → V → ℝ) (P : ℕ → List V) (hrun : IsShortestRun N K f P)
    (k l : ℕ) (hkl : k ≤ l) (hl : l ≤ K) (u : V) :
    resDist N (f k) N.s u ≤ resDist N (f l) N.s u ∧
    resDist N (f k) u N.t ≤ resDist N (f l) u N.t := by
  revert hl
  induction l, hkl using Nat.le_induction with
  | base => exact fun _ => ⟨le_rfl, le_rfl⟩
  | succ l hkl ih =>
    intro hl
    have hprev := ih (by omega)
    have hnext := resDist_monotone N K f P hrun l (by omega) u
    exact ⟨hprev.1.trans hnext.1, hprev.2.trans hnext.2⟩

private theorem local_resDist_shortest {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (f : V → V → ℝ) (P : List V) (hP : IsShortestAugPath N f P) :
    resDist N f N.s N.t = ((pathArcs P).length : ℕ∞) ∧
    1 ≤ (pathArcs P).length ∧ (pathArcs P).length < Fintype.card V := by
  have hlen : (pathArcs P).length = P.length - 1 := by simp [pathArcs]
  have hlong : 2 ≤ P.length := by
    cases P with
    | nil => simp [IsShortestAugPath, IsAugPath, IsDirPath] at hP
    | cons a T =>
      cases T with
      | nil =>
        have hs : a = N.s := by simpa using hP.1.2.1
        have ht : a = N.t := by simpa using hP.1.2.2.1
        exact (N.source_ne_sink (hs.symm.trans ht)).elim
      | cons b T => simp
  refine ⟨?_, ?_, ?_⟩
  · apply le_antisymm (iInf_le_of_le P (iInf_le_of_le hP.1 le_rfl))
    refine le_iInf fun Q => le_iInf fun hQ => ?_
    exact_mod_cast hP.2 Q hQ
  · omega
  · have hcard := hP.1.1.length_le_card
    omega

open Classical in
theorem solution {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (K : ℕ) (f : ℕ → V → V → ℝ) (P : ℕ → List V) (hrun : IsShortestRun N K f P) (u v : V) :
    2 * ((Finset.range K).filter (fun k =>
      IsBottleneck N (f k) (P k) u v ∨ IsBottleneck N (f k) (P k) v u)).card ≤ Fintype.card V + 1 := by
  classical
  let S := (Finset.range K).filter (fun k =>
    IsBottleneck N (f k) (P k) u v ∨ IsBottleneck N (f k) (P k) v u)
  apply local_card_le_of_gap_two S (fun k => (pathArcs (P k)).length) (Fintype.card V)
  · intro k hk
    have hkK := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
    exact (local_resDist_shortest N (f k) (P k) (hrun.2 k hkK).1).2.2
  · intro k hk l hl hkl
    obtain ⟨hkK, hbk⟩ := Finset.mem_filter.mp hk
    obtain ⟨hlK, hbl⟩ := Finset.mem_filter.mp hl
    have hkK := Finset.mem_range.mp hkK
    have hlK := Finset.mem_range.mp hlK
    have hsame (x y : V) (hb₁ : IsBottleneck N (f k) (P k) x y)
        (hb₂ : IsBottleneck N (f l) (P l) x y) :
        resDist N (f k) N.s N.t + 2 ≤ resDist N (f l) N.s N.t := by
      obtain ⟨j, hkj, hjl, hrev⟩ :=
        bottleneck_twice_reversed_between N K f P hrun k l hkl hlK x y hb₁ hb₂
      have hinc := resDist_add_two_of_reversed N K f P hrun k j hkj (by omega) x y hb₁.1 hrev
      exact hinc.trans (local_resDist_monotone_run N K f P hrun j l hjl.le hlK.le N.t).1
    have hdist : resDist N (f k) N.s N.t + 2 ≤ resDist N (f l) N.s N.t := by
      rcases hbk with hbk | hbk <;> rcases hbl with hbl | hbl
      · exact hsame u v hbk hbl
      · exact resDist_add_two_of_reversed N K f P hrun k l hkl hlK u v hbk.1 hbl.1
      · exact resDist_add_two_of_reversed N K f P hrun k l hkl hlK v u hbk.1 hbl.1
      · exact hsame v u hbk hbl
    rw [(local_resDist_shortest N (f k) (P k) (hrun.2 k hkK).1).1,
      (local_resDist_shortest N (f l) (P l) (hrun.2 l hlK).1).1] at hdist
    exact_mod_cast hdist
