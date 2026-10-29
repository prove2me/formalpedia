-- Prove2me | solution 1 for ChenWasserstein.Reform.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T04:35:15.716998+00:00
-- url     : https://prove2.me/submissions/62490727-5046-4eea-b383-c6cb0e524592

import Mathlib
import Definitions.Def_ChenWasserstein_Reform_Data

open ChenWasserstein.Reform

lemma s225mb_list_sum (L : List ℝ) (g : ℝ → ℝ) :
    (L.map g).sum = ∑ m ∈ Finset.range L.length, g (L.getD m 0) := by
  induction L with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, ih, List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    ring

lemma s225mb_fin_sum {N : ℕ} (k : Fin N → ℝ) (g : ℝ → ℝ) :
    ∑ i, g (k i) = ∑ m ∈ Finset.range N,
      g (((Finset.univ.val.map k).sort (· ≤ ·)).getD m 0) := by
  set L := (Finset.univ.val.map k).sort (· ≤ ·) with hL
  have hlen : L.length = N := by
    rw [hL, Multiset.length_sort]; simp
  rw [show Finset.range N = Finset.range L.length by rw [hlen], ← s225mb_list_sum,
    Finset.sum_eq_multiset_sum, ← Multiset.sum_coe, ← Multiset.map_coe, hL, Multiset.sort_eq,
    Multiset.map_map]
  rfl

theorem solution {N : ℕ} (k : Fin N → ℝ) (ε : ℝ)
    (hN : 0 < N) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ (s : Fin N → ℝ) (t : ℝ),
      (∀ i, 0 ≤ s i) ∧ (∀ i, t - s i ≤ k i) ∧
      ε * (N : ℝ) * t - ∑ i, s i = fractionalSmallest k (ε * (N : ℝ)) ∧
      ∀ (s' : Fin N → ℝ) (t' : ℝ),
        (∀ i, 0 ≤ s' i) → (∀ i, t' - s' i ≤ k i) →
        ε * (N : ℝ) * t' - ∑ i, s' i ≤ fractionalSmallest k (ε * (N : ℝ)) := by
  set ℓ := ε * (N : ℝ) with hℓ
  set J := ⌊ℓ⌋₊ with hJ
  set L := (Finset.univ.val.map k).sort (· ≤ ·) with hL
  have hlen : L.length = N := by
    rw [hL, Multiset.length_sort]; simp
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hℓ0 : 0 ≤ ℓ := by positivity
  have hℓN : ℓ < N := by rw [hℓ]; nlinarith
  have hJN : J < N := (Nat.floor_lt hℓ0).mpr hℓN
  have hJle : (J : ℝ) ≤ ℓ := Nat.floor_le hℓ0
  have hJlt : ℓ < J + 1 := Nat.lt_floor_add_one ℓ
  have hsorted : ∀ i j, i ≤ j → j < N → L.getD i 0 ≤ L.getD j 0 := by
    intro i j hij hj
    have hp : L.Pairwise (· ≤ ·) := Multiset.pairwise_sort _ _
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
    rcases eq_or_lt_of_le hij with h | h
    · subst h; exact le_rfl
    · exact List.pairwise_iff_getElem.mp hp i j (by omega) (by omega) h
  have hfrac : fractionalSmallest k ℓ =
      (∑ m ∈ Finset.range J, L.getD m 0) + (ℓ - J) * L.getD J 0 := by
    unfold fractionalSmallest WassDRCCP.Improved.kthSmallest
    rw [min_eq_left hJN.le, if_pos hJN]
  rw [hfrac]
  -- key lower bound on the hinge sum
  have hlow : ∀ t' : ℝ, (∑ m ∈ Finset.range J, (t' - L.getD m 0)) +
      (ℓ - J) * (t' - L.getD J 0) ≤ ∑ i, max (t' - k i) 0 := by
    intro t'
    rw [s225mb_fin_sum k (fun x => max (t' - x) 0)]
    have hsub : Finset.range (J + 1) ⊆ Finset.range N := Finset.range_subset_range.mpr hJN
    refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun _ _ _ => le_max_right _ _))
    rw [Finset.sum_range_succ, ← hL]
    apply add_le_add
    · exact Finset.sum_le_sum fun m _ => le_max_left _ _
    · set x := t' - L.getD J 0
      rcases le_or_gt 0 x with hx | hx
      · have : (ℓ - J) * x ≤ x := by nlinarith
        exact this.trans (le_max_left _ _)
      · have : (ℓ - J) * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hx.le
        exact this.trans (le_max_right _ _)
  refine ⟨fun i => max (L.getD J 0 - k i) 0, L.getD J 0, fun i => le_max_right _ _,
    fun i => by have := le_max_left (L.getD J 0 - k i) 0; linarith, ?_, ?_⟩
  · rw [s225mb_fin_sum k (fun x => max (L.getD J 0 - x) 0), ← hL]
    have hpt : ∀ m ∈ Finset.range N, max (L.getD J 0 - L.getD m 0) 0 =
        if m < J then L.getD J 0 - L.getD m 0 else 0 := by
      intro m hm
      rw [Finset.mem_range] at hm
      split_ifs with h
      · exact max_eq_left (by linarith [hsorted m J h.le hJN])
      · exact max_eq_right (by linarith [hsorted J m (by omega) hm])
    rw [Finset.sum_congr rfl hpt, ← Finset.sum_filter]
    have hf : (Finset.range N).filter (fun m => m < J) = Finset.range J := by
      ext m; simp only [Finset.mem_filter, Finset.mem_range]; omega
    rw [hf, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  · intro s' t' hs' ht'
    have h1 : ∑ i, max (t' - k i) 0 ≤ ∑ i, s' i :=
      Finset.sum_le_sum fun i _ => max_le (by linarith [ht' i]) (hs' i)
    have h2 := hlow t'
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h2
    nlinarith
