-- Prove2me | solution 1 for EmmonsTardiness.SPT.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T05:31:25.435984+00:00
-- url     : https://prove2.me/submissions/c4f1bd33-87d3-4d4e-9dc6-1278e7c2d096

import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime
import Definitions.Def_EmmonsTardiness_SPT_Model

set_option autoImplicit false

namespace EmmonsT1Aux

lemma idxOf_map_inj {ι : Type*} [DecidableEq ι] (f : ι → ι) (hf : Function.Injective f)
    (l : List ι) (y : ι) : (l.map f).idxOf (f y) = l.idxOf y := by
  induction l with
  | nil => simp
  | cons a t ih =>
    by_cases h : a = y
    · subst h; simp
    · have h' : f a ≠ f y := fun e => h (hf e)
      rw [List.map_cons, List.idxOf_cons_ne _ h', List.idxOf_cons_ne _ h, ih]

lemma prefix_formula {ι : Type*} [DecidableEq ι] (p : ι → ℝ) (l : List ι) (hl : l.Nodup)
    (j k : ι) (hj : j ∈ l) (hk : k ∈ l) (hab : l.idxOf k < l.idxOf j) (n : ℕ) :
    ((l.take n).map (p ∘ Equiv.swap j k)).sum =
      ((l.take n).map p).sum +
        (if l.idxOf k < n ∧ n ≤ l.idxOf j then p j - p k else 0) := by
  have ha := List.idxOf_lt_length_of_mem hk
  have hb := List.idxOf_lt_length_of_mem hj
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.take_add_one, List.map_append, List.map_append, List.sum_append, List.sum_append, ih]
    by_cases hn : n < l.length
    · rw [List.getElem?_eq_getElem hn]
      simp only [Option.toList_some, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero, Function.comp]
      by_cases h1 : n = l.idxOf k
      · have e : l[n] = k := by subst h1; exact List.getElem_idxOf ha
        rw [e, Equiv.swap_apply_right]
        split_ifs <;> first | (exfalso; omega) | ring
      · by_cases h2 : n = l.idxOf j
        · have e : l[n] = j := by subst h2; exact List.getElem_idxOf hb
          rw [e, Equiv.swap_apply_left]
          split_ifs <;> first | (exfalso; omega) | ring
        · have hne1 : l[n] ≠ k := by
            intro e; apply h1; rw [← e, hl.idxOf_getElem]
          have hne2 : l[n] ≠ j := by
            intro e; apply h2; rw [← e, hl.idxOf_getElem]
          rw [Equiv.swap_apply_of_ne_of_ne hne2 hne1]
          split_ifs <;> first | (exfalso; omega) | ring
    · rw [List.getElem?_eq_none (by omega)]
      simp only [Option.toList_none, List.map_nil, List.sum_nil, add_zero]
      split_ifs <;> first | (exfalso; omega) | ring

lemma arith (X Y pj pk dj dk : ℝ) (h1 : pj ≤ pk) (h2 : X ≤ Y) (h3 : dj ≤ dk ∨ dj ≤ X) :
    max 0 (X + (pj - pk) - dj) + max 0 (Y - dk) ≤ max 0 (Y - dj) + max 0 (X - dk) := by
  rcases h3 with h3 | h3 <;>
  · simp only [max_def]
    split_ifs <;> linarith

end EmmonsT1Aux

open EmmonsTardiness.SPT MooreLateJobs in
theorem solution {ι : Type*} [LinearOrder ι] (p d : ι → ℝ) (J : Finset ι)
    (hp : ∀ i ∈ J, 0 ≤ p i) (hidx : IsSPTIndexed p d J)
    (j k : ι) (hj : j ∈ J) (hk : k ∈ J) (hjk : j < k)
    (B : Finset ι) (hB : B ⊆ J) (hkB : k ∉ B)
    (h1 : ∃ l, IsOptimal p d J l ∧ ∀ i ∈ B, Precedes l i k)
    (h2 : d j ≤ max ((∑ i ∈ B, p i) + p k) (d k)) :
    ∃ l, IsOptimal p d J l ∧ (∀ i ∈ B, Precedes l i k) ∧ Precedes l j k := by
  obtain ⟨l, ⟨⟨hnd, hmem⟩, hopt⟩, hBl⟩ := h1
  by_cases hpre : Precedes l j k
  · exact ⟨l, ⟨⟨hnd, hmem⟩, hopt⟩, hBl, hpre⟩
  have hjl : j ∈ l := (hmem j).2 hj
  have hkl : k ∈ l := (hmem k).2 hk
  have hne : j ≠ k := ne_of_lt hjk
  have ha := List.idxOf_lt_length_of_mem hkl
  have hb := List.idxOf_lt_length_of_mem hjl
  have hab : l.idxOf k < l.idxOf j := by
    unfold Precedes at hpre
    have : l.idxOf j ≠ l.idxOf k := fun e => hne ((List.idxOf_inj hjl).1 e)
    omega
  set a := l.idxOf k with ha_def
  set b := l.idxOf j with hb_def
  set σ : Equiv.Perm ι := Equiv.swap j k with hσ
  have hσJ : ∀ y, σ y ∈ J ↔ y ∈ J := by
    intro y
    rw [hσ, Equiv.swap_apply_def]
    split_ifs with h h'
    · subst h; exact ⟨fun _ => hj, fun _ => hk⟩
    · subst h'; exact ⟨fun _ => hk, fun _ => hj⟩
    · exact Iff.rfl
  have hmem' : ∀ x, x ∈ l.map σ ↔ x ∈ J := by
    intro x
    rw [List.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact (hσJ y).2 ((hmem y).1 hy)
    · intro hx
      exact ⟨σ x, (hmem _).2 ((hσJ x).2 hx), Equiv.swap_apply_self _ _ _⟩
  have hidx' : ∀ x, (l.map σ).idxOf x = l.idxOf (σ x) := by
    intro x
    have := EmmonsT1Aux.idxOf_map_inj σ σ.injective l (σ x)
    rwa [show σ (σ x) = x from Equiv.swap_apply_self _ _ _] at this
  set F : ℕ → ℝ := fun n => ((l.take n).map p).sum with hF
  set G : ℕ → ℝ := fun n => ((l.take n).map (p ∘ σ)).sum with hG
  have hC : ∀ x, Shared.completionTime p l x = F (l.idxOf x + 1) := fun x => rfl
  have hC' : ∀ x, Shared.completionTime p (l.map σ) x = G (l.idxOf (σ x) + 1) := by
    intro x
    simp only [Shared.completionTime, Shared.completionAt, hidx', hG, ← List.map_take,
      List.map_map]
  have hGF : ∀ n, G n = F n + (if a < n ∧ n ≤ b then p j - p k else 0) := by
    intro n
    exact EmmonsT1Aux.prefix_formula p l hnd j k hjl hkl hab n
  have hpjk : p j ≤ p k := by
    rcases hidx j hj k hk hjk with h | h
    · exact h.le
    · exact h.1.le
  have hGle : ∀ n, G n ≤ F n := by
    intro n; rw [hGF n]; split_ifs <;> linarith
  have hFsucc : ∀ n, F n ≤ F (n + 1) := by
    intro n
    simp only [hF, List.take_add_one, List.map_append, List.sum_append]
    have : 0 ≤ ((l[n]?.toList).map p).sum := by
      apply List.sum_nonneg
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      rw [Option.mem_toList] at hy
      exact hp y ((hmem y).1 (List.mem_of_getElem? hy))
    linarith
  have hFmono : Monotone F := monotone_nat_of_le_succ hFsucc
  have hFa : F (a + 1) = F a + p k := by
    have e : l[a] = k := List.getElem_idxOf ha
    simp only [hF, List.take_add_one, List.getElem?_eq_getElem ha, e,
      Option.toList_some, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero]
  have hBF : (∑ i ∈ B, p i) ≤ F a := by
    have e : F a = ∑ x ∈ (l.take a).toFinset, p x :=
      (List.sum_toFinset p (hnd.sublist (List.take_sublist _ _))).symm
    rw [e]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro i hi
      have hil : i ∈ l := (hmem i).2 (hB hi)
      have hia : l.idxOf i < a := hBl i hi
      have hlt := List.idxOf_lt_length_of_mem hil
      rw [List.mem_toFinset]
      have hm : (l.take a)[l.idxOf i]'(by simp; omega) ∈ l.take a := List.getElem_mem _
      rwa [List.getElem_take, List.getElem_idxOf hlt] at hm
    · intro x hx _
      rw [List.mem_toFinset] at hx
      exact hp x ((hmem x).1 (List.mem_of_mem_take hx))
  have hσj : σ j = k := Equiv.swap_apply_left _ _
  have hσk : σ k = j := Equiv.swap_apply_right _ _
  have hTT : totalTardiness p d J (l.map σ) ≤ totalTardiness p d J l := by
    unfold totalTardiness tardiness
    have hkJ' : k ∈ J.erase j := Finset.mem_erase.2 ⟨hne.symm, hk⟩
    rw [← Finset.add_sum_erase J _ hj, ← Finset.add_sum_erase (J.erase j) _ hkJ',
      ← Finset.add_sum_erase J _ hj, ← Finset.add_sum_erase (J.erase j) _ hkJ']
    have hrest : ∑ x ∈ (J.erase j).erase k, max 0 (Shared.completionTime p (l.map σ) x - d x) ≤
        ∑ x ∈ (J.erase j).erase k, max 0 (Shared.completionTime p l x - d x) := by
      apply Finset.sum_le_sum
      intro x hx
      have hxk : x ≠ k := (Finset.mem_erase.1 hx).1
      have hxj : x ≠ j := (Finset.mem_erase.1 (Finset.mem_erase.1 hx).2).1
      have hσx : σ x = x := Equiv.swap_apply_of_ne_of_ne hxj hxk
      rw [hC', hC, hσx]
      exact max_le_max le_rfl (by linarith [hGle (l.idxOf x + 1)])
    have hkey : max 0 (Shared.completionTime p (l.map σ) j - d j) +
        max 0 (Shared.completionTime p (l.map σ) k - d k) ≤
        max 0 (Shared.completionTime p l j - d j) + max 0 (Shared.completionTime p l k - d k) := by
      rw [hC', hC', hC, hC, hσj, hσk, ← ha_def, ← hb_def]
      have g1 : G (a + 1) = F (a + 1) + (p j - p k) := by
        rw [hGF]; rw [if_pos (by omega)]
      have g2 : G (b + 1) = F (b + 1) := by
        rw [hGF]; rw [if_neg (by omega), add_zero]
      rw [g1, g2]
      have hXY : F (a + 1) ≤ F (b + 1) := hFmono (by omega)
      have h3 : d j ≤ d k ∨ d j ≤ F (a + 1) := by
        rcases le_max_iff.1 h2 with h | h
        · right; linarith
        · left; exact h
      have := EmmonsT1Aux.arith (F (a + 1)) (F (b + 1)) (p j) (p k) (d j) (d k) hpjk hXY h3
      linarith
    linarith
  refine ⟨l.map σ, ⟨⟨hnd.map σ.injective, hmem'⟩, ?_⟩, ?_, ?_⟩
  · intro l' hl'
    exact le_trans hTT (hopt l' hl')
  · intro i hi
    have hik : i ≠ k := fun e => hkB (e ▸ hi)
    have hij : i ≠ j := by
      intro e; apply hpre; rw [← e]; exact hBl i hi
    unfold Precedes
    rw [hidx', hidx', Equiv.swap_apply_of_ne_of_ne hij hik, hσk]
    have := hBl i hi
    unfold Precedes at this
    omega
  · unfold Precedes
    rw [hidx', hidx', hσj, hσk]
    exact hab
