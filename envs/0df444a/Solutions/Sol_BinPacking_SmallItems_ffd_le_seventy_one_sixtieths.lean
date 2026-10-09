-- Prove2me | solution 1 for BinPacking.SmallItems.ffd_le_seventy_one_sixtieths
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T18:51:12.710131+00:00
-- url     : https://prove2.me/submissions/cf55a4a7-9375-4521-97d4-1c6a82b973b9

import Mathlib
import Definitions.Def_BinPacking_SmallItems_Model
import Definitions.Def_BinPacking_SmallItems_Weight
import Theorems.Thm_BinPacking_SmallItems_ffd_filter_preserves_excess
import Theorems.Thm_BinPacking_SmallItems_W_ge_ffd_sub
import Theorems.Thm_BinPacking_SmallItems_W_flatten_le_sum
import Theorems.Thm_BinPacking_SmallItems_W_le_seventy_one_sixtieths

set_option autoImplicit false

namespace BinPackingFFD71

open BinPacking.SmallItems

/-- `W` as a function of the sorted list. -/
noncomputable def Wlist (A : List ℝ) : ℝ :=
  (pairings A.length).inf' ⟨1, by simp [pairings]⟩ (w12 A)

theorem W_eq_Wlist (X : List ℝ) : W X = Wlist (sortDesc X) := rfl

theorem sortDesc_pairwise (L : List ℝ) : (sortDesc L).Pairwise (fun a b => b ≤ a) := by
  have := List.pairwise_mergeSort (le := fun a b : ℝ => decide (b ≤ a))
    (fun a b c h1 h2 => by simp at h1 h2 ⊢; linarith)
    (fun a b => by simp; exact le_total b a) L
  exact this.imp (fun h => by simpa using h)

theorem sortDesc_perm (L : List ℝ) : (sortDesc L).Perm L := List.mergeSort_perm _ _

/-- `W` only depends on the multiset of values. -/
theorem W_perm {X Y : List ℝ} (h : X.Perm Y) : W X = W Y := by
  have hs : sortDesc X = sortDesc Y :=
    List.Perm.eq_of_pairwise (le := fun a b : ℝ => b ≤ a) (fun a b _ _ h1 h2 => le_antisymm h2 h1)
      (sortDesc_pairwise X) (sortDesc_pairwise Y)
      (((sortDesc_perm X).trans h).trans (sortDesc_perm Y).symm)
  rw [W_eq_Wlist, W_eq_Wlist, hs]

theorem sum_map_filter_eq {α : Type} (l : List α) (P : α → Prop) [DecidablePred P] (g : α → ℝ) :
    ((l.filter (fun a => decide (P a))).map g).sum = (l.map fun a => if P a then g a else 0).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases h : P a <;> simp [h, ih]

theorem perm_flatten_bins {α : Type} [DecidableEq α] (l : List α) (b : ℕ) (f : α → Fin b) :
    l.Perm ((List.finRange b).map fun j => l.filter (fun a => decide (f a = j))).flatten := by
  rw [List.perm_iff_count]
  intro a
  rw [List.count_flatten, List.map_map]
  have : ∀ j : Fin b, (List.count a ∘ fun j => l.filter (fun a => decide (f a = j))) j =
      if f a = j then l.count a else 0 := by
    intro j
    by_cases h : f a = j
    · simp only [Function.comp, if_pos h]
      rw [List.count_filter]
      simp [h]
    · simp only [Function.comp, if_neg h]
      exact List.count_eq_zero.2 (by simp [h])
  rw [List.map_congr_left (fun j _ => this j), ← Fin.sum_univ_def]
  simp

theorem exists_bins (L : List ℝ) (hL : IsList L) :
    ∃ f : Fin L.length → Fin (optBins L),
      ∀ j : Fin (optBins L), ∑ i ∈ Finset.univ.filter (fun i => f i = j), L.get i ≤ 1 := by
  have hne : {b : ℕ | ∃ f : Fin L.length → Fin b, ∀ j : Fin b,
      ∑ i ∈ Finset.univ.filter (fun i => f i = j), L.get i ≤ 1}.Nonempty := by
    refine ⟨L.length, id, fun j => ?_⟩
    have : Finset.univ.filter (fun i : Fin L.length => id i = j) = {j} := by
      ext i; simp
    rw [this, Finset.sum_singleton]
    exact (hL _ (List.get_mem _ _)).2
  exact Nat.sInf_mem hne

theorem W_le_of_bins (L : List ℝ) (hL : IsList L) (hr : ∀ a ∈ L, 1 / 7 < a ∧ a ≤ 1 / 2)
    (b : ℕ) (f : Fin L.length → Fin b)
    (hf : ∀ j : Fin b, ∑ i ∈ Finset.univ.filter (fun i => f i = j), L.get i ≤ 1) :
    W L ≤ 71 / 60 * (b : ℝ) := by
  let Xs : List (List ℝ) := (List.finRange b).map fun j =>
    ((List.finRange L.length).filter (fun i => decide (f i = j))).map L.get
  have hperm : L.Perm Xs.flatten := by
    have h1 := perm_flatten_bins (List.finRange L.length) b f
    have h2 := h1.map L.get
    have h3 : (List.finRange L.length).map L.get = L := by
      rw [← List.ofFn_eq_map, List.ofFn_get]
    rw [h3, List.map_flatten, List.map_map] at h2
    exact h2
  have hmem : ∀ X ∈ Xs, ∀ a ∈ X, a ∈ L := by
    intro X hX a ha
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hX
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 ha
    exact List.get_mem _ _
  have hflat : IsList Xs.flatten := fun a ha => hL a (hperm.symm.subset ha)
  have hsum : ∀ X ∈ Xs, X.sum ≤ 1 := by
    intro X hX
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hX
    rw [sum_map_filter_eq (List.finRange L.length) (fun i => f i = j) L.get]
    have := hf j
    rw [Finset.sum_filter, Fin.sum_univ_def] at this
    exact this
  have hXW : ∀ X ∈ Xs, W X ≤ 71 / 60 := by
    intro X hX
    exact W_le_seventy_one_sixtieths X (fun x hx => hr x (hmem X hX x hx)) (hsum X hX)
  have hlen : Xs.length = b := by simp [Xs]
  calc W L = W Xs.flatten := W_perm hperm
    _ ≤ (Xs.map W).sum := W_flatten_le_sum Xs hflat
    _ ≤ Xs.length • (71 / 60 : ℝ) := by
        have := List.sum_le_card_nsmul (Xs.map W) (71 / 60 : ℝ) (fun w hw => by
          obtain ⟨X, hX, rfl⟩ := List.mem_map.1 hw
          exact hXW X hX)
        rwa [List.length_map] at this
    _ = 71 / 60 * (b : ℝ) := by rw [hlen, nsmul_eq_mul]; ring

theorem W_le_opt (L : List ℝ) (hL : IsList L) (hr : ∀ a ∈ L, 1 / 7 < a ∧ a ≤ 1 / 2) :
    W L ≤ 71 / 60 * (optBins L : ℝ) := by
  obtain ⟨f, hf⟩ := exists_bins L hL
  exact W_le_of_bins L hL hr (optBins L) f hf

end BinPackingFFD71

open BinPacking.SmallItems BinPackingFFD71 in
theorem solution (L : List ℝ) (hL : IsList L) (hhalf : ∀ a ∈ L, a ≤ 1 / 2) :
    (FFD L : ℝ) ≤ 71 / 60 * (optBins L : ℝ) + 5 := by
  by_contra hcon
  replace hcon := not_le.mp hcon
  have key := ffd_filter_preserves_excess (71 / 60) 5 (by norm_num) (by norm_num) L hL hcon
  set L' := L.filter (fun a => decide ((71 / 60 - 1) / (71 / 60 : ℝ) < a)) with hL'def
  have hmem : ∀ a ∈ L', a ∈ L ∧ 11 / 71 < a := by
    intro a ha
    rw [hL'def, List.mem_filter, decide_eq_true_eq] at ha
    exact ⟨ha.1, by have := ha.2; norm_num at this; linarith⟩
  have hL'1 : IsList L' := fun a ha => hL a (hmem a ha).1
  have hr : ∀ a ∈ L', 1 / 7 < a ∧ a ≤ 1 / 2 := fun a ha =>
    ⟨by have := (hmem a ha).2; linarith, hhalf a (hmem a ha).1⟩
  have hW := W_ge_ffd_sub 7 (by norm_num) L' hL'1 (fun a ha => by
    have := hr a ha
    push_cast
    exact this)
  have hup := W_le_opt L' hL'1 hr
  push_cast at hW
  linarith
