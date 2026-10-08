-- Prove2me | solution 1 for CuttingStock63.Knapsack.tested_vector_invariant
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T15:04:38.72792+00:00
-- url     : https://prove2.me/submissions/79ceb3c6-e904-4681-af87-1114620592a0

import Mathlib
import Definitions.Def_CuttingStock63_Knapsack_Problem
import Definitions.Def_CuttingStock63_Knapsack_Method



namespace CuttingStock63.Knapsack

theorem lam_eq_ite {m : ℕ} (l : Fin m → ℝ) (a : Fin m → ℕ) (s : ℕ) :
    lam l a s = ∑ i : Fin m, if i.val < s then l i * (a i : ℝ) else 0 := by
  unfold lam; rw [Finset.sum_filter]

theorem bet_eq_ite {m : ℕ} (b : Fin m → ℝ) (a : Fin m → ℕ) (s : ℕ) :
    bet b a s = ∑ i : Fin m, if i.val < s then b i * (a i : ℝ) else 0 := by
  unfold bet; rw [Finset.sum_filter]

theorem lam_full {m : ℕ} (l : Fin m → ℝ) (a : Fin m → ℕ) :
    lam l a m = ∑ i : Fin m, l i * (a i : ℝ) := by
  rw [lam_eq_ite]; exact Finset.sum_congr rfl (fun i _ => by simp [i.isLt])

theorem bet_full {m : ℕ} (b : Fin m → ℝ) (a : Fin m → ℕ) :
    bet b a m = ∑ i : Fin m, b i * (a i : ℝ) := by
  rw [bet_eq_ite]; exact Finset.sum_congr rfl (fun i _ => by simp [i.isLt])

theorem lam_congr {m : ℕ} (l : Fin m → ℝ) (a a' : Fin m → ℕ) (s : ℕ)
    (h : ∀ i : Fin m, i.val < s → a' i = a i) : lam l a' s = lam l a s := by
  rw [lam_eq_ite, lam_eq_ite]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases hi : i.val < s
  · simp [hi, h i hi]
  · simp [hi]

theorem bet_congr {m : ℕ} (b : Fin m → ℝ) (a a' : Fin m → ℕ) (s : ℕ)
    (h : ∀ i : Fin m, i.val < s → a' i = a i) : bet b a' s = bet b a s := by
  rw [bet_eq_ite, bet_eq_ite]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases hi : i.val < s
  · simp [hi, h i hi]
  · simp [hi]

theorem lam_nonneg {m : ℕ} (l : Fin m → ℝ) (hl : ∀ i, 0 < l i) (a : Fin m → ℕ) (s : ℕ) :
    0 ≤ lam l a s := by
  rw [lam_eq_ite]
  exact Finset.sum_nonneg (fun i _ => by
    by_cases hi : i.val < s
    · simp only [hi, if_true]; exact mul_nonneg (hl i).le (Nat.cast_nonneg _)
    · simp [hi])

theorem lam_mono {m : ℕ} (l : Fin m → ℝ) (hl : ∀ i, 0 < l i) (a : Fin m → ℕ) {s s' : ℕ}
    (h : s ≤ s') : lam l a s ≤ lam l a s' := by
  rw [lam_eq_ite, lam_eq_ite]
  refine Finset.sum_le_sum (fun i _ => ?_)
  by_cases hi : i.val < s
  · simp only [hi, if_true, show i.val < s' from lt_of_lt_of_le hi h]; exact le_rfl
  · by_cases hi' : i.val < s'
    · simp only [hi, hi', if_true, if_false]; exact mul_nonneg (hl i).le (Nat.cast_nonneg _)
    · simp [hi, hi']

theorem lam_succ {m : ℕ} (l : Fin m → ℝ) (a : Fin m → ℕ) (p : ℕ) (hp : p < m) :
    lam l a (p + 1) = lam l a p + l ⟨p, hp⟩ * (a ⟨p, hp⟩ : ℝ) := by
  rw [lam_eq_ite, lam_eq_ite]
  have : ∀ i : Fin m, (if i.val < p + 1 then l i * (a i : ℝ) else 0) =
      (if i.val < p then l i * (a i : ℝ) else 0) +
        (if i = ⟨p, hp⟩ then l i * (a i : ℝ) else 0) := by
    intro i
    by_cases h1 : i.val < p
    · have : i ≠ ⟨p, hp⟩ := fun h => by rw [h] at h1; simp at h1
      simp [h1, this, show i.val < p + 1 by omega]
    · by_cases h2 : i = ⟨p, hp⟩
      · subst h2; simp
      · have : ¬ i.val < p + 1 := by
          intro h3
          apply h2; apply Fin.ext; simp; omega
        simp [h1, h2, this]
  rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single ⟨p, hp⟩]
  · simp
  · intro i _ hi; simp [hi]
  · simp

theorem bet_succ {m : ℕ} (b : Fin m → ℝ) (a : Fin m → ℕ) (p : ℕ) (hp : p < m) :
    bet b a (p + 1) = bet b a p + b ⟨p, hp⟩ * (a ⟨p, hp⟩ : ℝ) := by
  rw [bet_eq_ite, bet_eq_ite]
  have : ∀ i : Fin m, (if i.val < p + 1 then b i * (a i : ℝ) else 0) =
      (if i.val < p then b i * (a i : ℝ) else 0) +
        (if i = ⟨p, hp⟩ then b i * (a i : ℝ) else 0) := by
    intro i
    by_cases h1 : i.val < p
    · have : i ≠ ⟨p, hp⟩ := fun h => by rw [h] at h1; simp at h1
      simp [h1, this, show i.val < p + 1 by omega]
    · by_cases h2 : i = ⟨p, hp⟩
      · subst h2; simp
      · have : ¬ i.val < p + 1 := by
          intro h3
          apply h2; apply Fin.ext; simp; omega
        simp [h1, h2, this]
  rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single ⟨p, hp⟩]
  · simp
  · intro i _ hi; simp [hi]
  · simp

theorem nextL_pos {m : ℕ} (l : Fin m → ℝ) (hl : ∀ i, 0 < l i) (s : ℕ) : 0 < nextL l s := by
  unfold nextL; split_ifs with h
  · exact hl _
  · exact one_pos

theorem nextB_nonneg {m : ℕ} (b : Fin m → ℝ) (hb : ∀ i, 0 ≤ b i) (s : ℕ) : 0 ≤ nextB b s := by
  unfold nextB; split_ifs with h
  · exact hb _
  · exact le_rfl

/-- density bound: items at index ≥ s have b_i ≤ (nextB/nextL) * l_i -/
theorem dens_bound {m : ℕ} (l b : Fin m → ℝ) (hl : ∀ i, 0 < l i) (hb : ∀ i, 0 ≤ b i)
    (hdens : ∀ i i' : Fin m, i ≤ i' → b i' / l i' ≤ b i / l i) (s : ℕ) (i : Fin m)
    (hi : s ≤ i.val) : b i ≤ (nextB b s / nextL l s) * l i := by
  unfold nextB nextL
  have hs : s < m := lt_of_le_of_lt hi i.isLt
  simp only [hs, dif_pos]
  have := hdens ⟨s, hs⟩ i (by exact Fin.mk_le_mk.mpr hi)
  rw [div_le_div_iff₀ (hl i) (hl _)] at this
  rw [div_mul_eq_mul_div, le_div_iff₀ (hl _)]
  linarith

theorem relaxation_core {m : ℕ} (l b : Fin m → ℝ) (hl : ∀ i, 0 < l i) (hb : ∀ i, 0 ≤ b i)
    (hdens : ∀ i i' : Fin m, i ≤ i' → b i' / l i' ≤ b i / l i) (L : ℝ) (a : Fin m → ℕ)
    (s : ℕ) (hs1 : 1 ≤ s) (hsm : s ≤ m) (a' : Fin m → ℕ) (hext : IsExtension a a' s)
    (hfit : Fits l L a') :
    bet b a' m ≤ bet b a s + nextB b s * (L - lam l a s) / nextL l s := by
  set r := nextB b s / nextL l s with hr
  have hr0 : 0 ≤ r := div_nonneg (nextB_nonneg b hb s) (nextL_pos l hl s).le
  have hrw : nextB b s * (L - lam l a s) / nextL l s = r * (L - lam l a s) := by
    rw [hr]; ring
  rw [hrw]
  have h1 : bet b a' s = bet b a s := bet_congr b a a' s hext
  have h2 : lam l a' s = lam l a s := lam_congr l a a' s hext
  have key : bet b a' m - bet b a' s ≤ r * (lam l a' m - lam l a' s) := by
    rw [bet_eq_ite, bet_eq_ite, lam_eq_ite, lam_eq_ite, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    by_cases hi : i.val < s
    · simp [hi, i.isLt]
    · simp only [hi, i.isLt, if_true, if_false, sub_zero]
      have := dens_bound l b hl hb hdens s i (not_lt.mp hi)
      have h3 : b i * (a' i : ℝ) ≤ r * l i * (a' i : ℝ) :=
        mul_le_mul_of_nonneg_right this (Nat.cast_nonneg _)
      linarith
  have hfit' : lam l a' m ≤ L := hfit
  have : r * (lam l a' m - lam l a' s) ≤ r * (L - lam l a s) := by
    apply mul_le_mul_of_nonneg_left _ hr0
    linarith
  linarith

theorem successor_core {m : ℕ} (l b : Fin m → ℝ) (hl : ∀ i, 0 < l i) (hb : ∀ i, 0 ≤ b i)
    (hdens : ∀ i i' : Fin m, i ≤ i' → b i' / l i' ≤ b i / l i) (L M : ℝ) (a : Fin m → ℕ)
    (s : ℕ) (hs1 : 1 ≤ s) (hsm : s ≤ m)
    (hfail : (L - lam l a s) * nextB b s ≤ (M - bet b a s) * nextL l s)
    (a' : Fin m → ℕ) (hpre : ∀ i : Fin m, i.val + 1 < s → a' i = a i)
    (hlast : ∀ i : Fin m, i.val + 1 = s → a' i ≤ a i) (hfit : Fits l L a') :
    bet b a' m ≤ M := by
  obtain ⟨p, rfl⟩ : ∃ p, s = p + 1 := ⟨s - 1, by omega⟩
  have hp : p < m := by omega
  set r := nextB b (p + 1) / nextL l (p + 1) with hr
  have hr0 : 0 ≤ r := div_nonneg (nextB_nonneg b hb _) (nextL_pos l hl _).le
  have hnl := nextL_pos l hl (p + 1)
  have hfail' : r * (L - lam l a (p + 1)) ≤ M - bet b a (p + 1) := by
    rw [hr, div_mul_eq_mul_div, div_le_iff₀ hnl]; linarith
  have hrel := relaxation_core l b hl hb hdens L a' (p + 1) hs1 hsm a' (fun _ _ => rfl) hfit
  have hrw : nextB b (p + 1) * (L - lam l a' (p + 1)) / nextL l (p + 1)
      = r * (L - lam l a' (p + 1)) := by rw [hr]; ring
  rw [hrw] at hrel
  have e1 : lam l a' p = lam l a p := lam_congr l a a' p (fun i hi => hpre i (by omega))
  have e2 : bet b a' p = bet b a p := bet_congr b a a' p (fun i hi => hpre i (by omega))
  rw [lam_succ l a' p hp, e1] at hrel
  rw [lam_succ l a p hp] at hfail'
  rw [bet_succ b a' p hp, e2] at hrel
  rw [bet_succ b a p hp] at hfail'
  have hle : a' ⟨p, hp⟩ ≤ a ⟨p, hp⟩ := hlast ⟨p, hp⟩ rfl
  have hle' : (a' ⟨p, hp⟩ : ℝ) ≤ (a ⟨p, hp⟩ : ℝ) := by exact_mod_cast hle
  have hd : r * l ⟨p, hp⟩ ≤ b ⟨p, hp⟩ := by
    by_cases hpm : p + 1 < m
    · have := hdens ⟨p, hp⟩ ⟨p + 1, hpm⟩ (by exact Fin.mk_le_mk.mpr (by omega))
      rw [hr]; unfold nextB nextL; simp only [hpm, dif_pos]
      rw [div_le_div_iff₀ (hl _) (hl _)] at this
      rw [div_mul_eq_mul_div, div_le_iff₀ (hl _)]
      nlinarith
    · have : nextB b (p + 1) = 0 := by unfold nextB; simp [hpm]
      rw [hr, this]; simp; exact hb _
  have hbl := mul_le_mul_of_nonneg_left hle' (sub_nonneg.mpr hd)
  nlinarith [hbl]


theorem identical_core {m : ℕ} (l b : Fin m → ℝ) (L : ℝ) (i j : Fin m) (hij : i ≠ j)
    (hlt : l i < l j) (hbeq : b i = b j) (a : Fin m → ℕ) (ha : Fits l L a) :
    ∃ a' : Fin m → ℕ, Fits l L a' ∧ a' j = 0 ∧ bet b a' m = bet b a m := by
  classical
  refine ⟨fun x => if x = j then 0 else if x = i then a i + a j else a x, ?_, by simp, ?_⟩
  · show lam l _ m ≤ L
    refine le_trans ?_ ha
    rw [lam_full, lam_full]
    have : ∀ x : Fin m, l x * ((if x = j then 0 else if x = i then a i + a j else a x : ℕ) : ℝ)
        = l x * (a x : ℝ) + (Pi.single i (l i * (a j : ℝ)) : Fin m → ℝ) x + (Pi.single j (-(l j * (a j : ℝ))) : Fin m → ℝ) x := by
      intro x
      by_cases hxj : x = j
      · subst hxj; simp [Pi.single_apply, hij.symm]
      · by_cases hxi : x = i
        · subst hxi; simp [Pi.single_apply, hxj]; push_cast; ring
        · simp [Pi.single_apply, hxj, hxi]
    rw [Finset.sum_congr rfl (fun x _ => this x), Finset.sum_add_distrib, Finset.sum_add_distrib]
    simp only [Finset.sum_pi_single', Finset.mem_univ, if_true]
    have : 0 ≤ (l j - l i) * (a j : ℝ) := mul_nonneg (by linarith) (Nat.cast_nonneg _)
    linarith
  · rw [bet_full, bet_full]
    have : ∀ x : Fin m, b x * ((if x = j then 0 else if x = i then a i + a j else a x : ℕ) : ℝ)
        = b x * (a x : ℝ) + (Pi.single i (b i * (a j : ℝ)) : Fin m → ℝ) x + (Pi.single j (-(b j * (a j : ℝ))) : Fin m → ℝ) x := by
      intro x
      by_cases hxj : x = j
      · subst hxj; simp [Pi.single_apply, hij.symm]
      · by_cases hxi : x = i
        · subst hxi; simp [Pi.single_apply, hxj]; push_cast; ring
        · simp [Pi.single_apply, hxj, hxi]
    rw [Finset.sum_congr rfl (fun x _ => this x), Finset.sum_add_distrib, Finset.sum_add_distrib]
    simp only [Finset.sum_pi_single', Finset.mem_univ, if_true]
    rw [hbeq]; ring


theorem lexlt {m : ℕ} (a b : Fin m → ℕ) :
    toLex a < toLex b ↔ ∃ i, (∀ j, j < i → a j = b j) ∧ a i < b i := Iff.rfl

theorem lexlt' {m : ℕ} (a b : Fin m → ℕ) (i : Fin m) (h1 : ∀ j, j < i → a j = b j)
    (h2 : a i < b i) : toLex a < toLex b := ⟨i, h1, h2⟩

theorem greedy_fold_inv {m : ℕ} (l : Fin m → ℝ) (hl : ∀ i, 0 < l i) (cap : ℝ)
    (a : Fin m → ℕ) (s : ℕ) :
    ∀ n, n ≤ m →
      let p := ((List.finRange m).take n).foldl
        (fun (acc : (Fin m → ℕ) × ℝ) (i : Fin m) =>
          if i.val < s then acc
          else
            let q : ℕ := ⌊(cap - acc.2) / l i⌋₊
            (Function.update acc.1 i q, acc.2 + l i * (q : ℝ)))
        (a, lam l a s)
      (∀ i : Fin m, n ≤ i.val → p.1 i = a i) ∧ (∀ i : Fin m, i.val < s → p.1 i = a i) ∧
        p.2 = lam l p.1 (max n s) ∧
        (∀ i : Fin m, s ≤ i.val → i.val < n → p.1 i = ⌊(cap - lam l p.1 i.val) / l i⌋₊) := by
  intro n
  induction n with
  | zero =>
    intro _
    simp only [List.take_zero, List.foldl_nil]
    simp
  | succ n ih =>
    intro hn
    have hnm : n < m := hn
    obtain ⟨h1, h2, h3, h4⟩ := ih (le_of_lt hnm)
    have htake : (List.finRange m).take (n+1) = (List.finRange m).take n ++ [⟨n,hnm⟩] := by
      rw [List.take_add_one]; simp [hnm]
    rw [htake, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    set p := ((List.finRange m).take n).foldl
        (fun (acc : (Fin m → ℕ) × ℝ) (i : Fin m) =>
          if i.val < s then acc
          else
            let q : ℕ := ⌊(cap - acc.2) / l i⌋₊
            (Function.update acc.1 i q, acc.2 + l i * (q : ℝ)))
        (a, lam l a s) with hp
    clear_value p
    by_cases hns : n < s
    · simp only [show (⟨n, hnm⟩ : Fin m).val < s from hns, if_true]
      refine ⟨fun i hi => h1 i (by omega), h2, ?_, fun i hi1 hi2 => ?_⟩
      · rw [h3]; congr 1; omega
      · have := h4 i hi1 (by omega)
        exact absurd hi2 (by omega)
    · simp only [show ¬ (⟨n, hnm⟩ : Fin m).val < s from hns, if_false]
      have hmax : max n s = n := by omega
      rw [hmax] at h3
      have hAn : ∀ i : Fin m, i.val < n → Function.update p.1 ⟨n,hnm⟩
          (⌊(cap - p.2) / l ⟨n,hnm⟩⌋₊) i = p.1 i := by
        intro i hi
        apply Function.update_of_ne
        intro h; rw [h] at hi; simp at hi
      refine ⟨fun i hi => ?_, fun i hi => ?_, ?_, fun i hi1 hi2 => ?_⟩
      · rw [Function.update_of_ne (fun h => by rw [h] at hi; simp at hi)]
        exact h1 i (by omega)
      · rw [Function.update_of_ne (fun h => hns (by rw [h] at hi; exact hi))]
        exact h2 i hi
      · have hmax' : max (n+1) s = n + 1 := by omega
        rw [hmax', lam_succ l _ n hnm]
        have : lam l (Function.update p.1 ⟨n,hnm⟩ (⌊(cap - p.2) / l ⟨n,hnm⟩⌋₊)) n = lam l p.1 n :=
          lam_congr l _ _ n hAn
        rw [this, h3]
        simp
      · by_cases hin : i.val < n
        · rw [hAn i hin, h4 i hi1 hin]
          rw [lam_congr l p.1 _ i.val (fun j hj => hAn j (by omega))]
        · have : i = ⟨n, hnm⟩ := Fin.ext (by simp; omega)
          subst this
          have e : lam l (Function.update p.1 ⟨n,hnm⟩ (⌊(cap - p.2) / l ⟨n,hnm⟩⌋₊)) n = lam l p.1 n :=
            lam_congr l _ _ n hAn
          simp only [Function.update_self]
          rw [e, h3]

theorem greedy_char {m : ℕ} (l : Fin m → ℝ) (hl : ∀ i, 0 < l i) (cap : ℝ)
    (a : Fin m → ℕ) (s : ℕ) :
    (∀ i : Fin m, i.val < s → greedyFill l cap a s i = a i) ∧
    (∀ i : Fin m, s ≤ i.val →
      greedyFill l cap a s i = ⌊(cap - lam l (greedyFill l cap a s) i.val) / l i⌋₊) := by
  have := greedy_fold_inv l hl cap a s m le_rfl
  rw [List.take_of_length_le (by simp)] at this
  obtain ⟨h1, h2, h3, h4⟩ := this
  exact ⟨h2, fun i hi => h4 i hi i.isLt⟩

theorem greedy_core {m : ℕ} (l : Fin m → ℝ) (hl : ∀ i, 0 < l i) (cap : ℝ)
    (a : Fin m → ℕ) (s : ℕ) (hs : s ≤ m) (hfit : lam l a s ≤ cap) :
    IsExtension a (greedyFill l cap a s) s ∧ Fits l cap (greedyFill l cap a s) ∧
      ∀ a' : Fin m → ℕ, IsExtension a a' s → Fits l cap a' →
        toLex a' ≤ toLex (greedyFill l cap a s) := by
  obtain ⟨hc1, hc2⟩ := greedy_char l hl cap a s
  set G := greedyFill l cap a s with hG
  clear_value G
  have hext : IsExtension a G s := hc1
  refine ⟨hext, ?_, ?_⟩
  · -- fits
    have key : ∀ n, s ≤ n → n ≤ m → lam l G n ≤ cap := by
      intro n hsn
      induction n, hsn using Nat.le_induction with
      | base =>
        intro _
        rw [lam_congr l a G s hc1]; exact hfit
      | succ n hsn ih =>
        intro hn
        have hnm : n < m := hn
        have ih' := ih (le_of_lt hnm)
        rw [lam_succ l G n hnm]
        have hq := hc2 ⟨n, hnm⟩ hsn
        simp only at hq
        rw [hq]
        have hpos : 0 ≤ (cap - lam l G n) / l ⟨n,hnm⟩ :=
          div_nonneg (by linarith) (hl _).le
        have := Nat.floor_le hpos
        have h2 : l ⟨n,hnm⟩ * ((⌊(cap - lam l G n) / l ⟨n,hnm⟩⌋₊ : ℕ) : ℝ)
            ≤ l ⟨n,hnm⟩ * ((cap - lam l G n) / l ⟨n,hnm⟩) :=
          mul_le_mul_of_nonneg_left this (hl _).le
        rw [mul_div_cancel₀ _ (hl _).ne'] at h2
        linarith
    exact key m hs le_rfl
  · intro a' ha' hfit'
    by_contra hcon
    have hlt : toLex G < toLex a' := lt_of_not_ge hcon
    obtain ⟨i, hi1, hi2⟩ := (lexlt G a').mp hlt
    by_cases his : i.val < s
    · have := ha' i his
      have := hext i his
      omega
    · have his' : s ≤ i.val := not_lt.mp his
      have hcong : lam l a' i.val = lam l G i.val :=
        lam_congr l G a' i.val (fun j hj => (hi1 j (by exact hj)).symm)
      have hle : lam l a' (i.val + 1) ≤ cap :=
        le_trans (lam_mono l hl a' (by have := i.isLt; omega)) hfit'
      rw [lam_succ l a' i.val i.isLt, hcong] at hle
      have hle2 : (a' i : ℝ) ≤ (cap - lam l G i.val) / l i := by
        rw [le_div_iff₀ (hl i)]
        have : (⟨i.val, i.isLt⟩ : Fin m) = i := rfl
        simp only [this] at hle
        nlinarith
      have h3 : a' i ≤ ⌊(cap - lam l G i.val) / l i⌋₊ := Nat.le_floor hle2
      rw [← hc2 i his'] at h3
      omega


theorem decrAt_apply {m : ℕ} (a : Fin m → ℕ) (s : ℕ) (j : Fin m) :
    decrAt a s j = if j.val + 1 = s then a j - 1 else a j := rfl

theorem decr_lam_le {m : ℕ} (l : Fin m → ℝ) (hl : ∀ i, 0 < l i) (a : Fin m → ℕ) (s n : ℕ) :
    lam l (decrAt a s) n ≤ lam l a n := by
  rw [lam_eq_ite, lam_eq_ite]
  refine Finset.sum_le_sum (fun i _ => ?_)
  by_cases hi : i.val < n
  · simp only [hi, if_true]
    apply mul_le_mul_of_nonneg_left _ (hl i).le
    rw [decrAt_apply]
    split_ifs
    · exact_mod_cast Nat.sub_le _ _
    · exact le_rfl
  · simp [hi]

theorem lex_pred_core {m : ℕ} (l : Fin m → ℝ) (hl : ∀ i, 0 < l i) (cap : ℝ)
    (a : Fin m → ℕ) (hfit : Fits l cap a) (i : Fin m) (hi : a i ≠ 0)
    (hmax : ∀ i' : Fin m, i < i' → a i' = 0) :
    (∃ g : Fin m → ℕ, Fits l cap g ∧ toLex g < toLex a ∧
        ∀ a' : Fin m → ℕ, Fits l cap a' → toLex a' < toLex a → toLex a' ≤ toLex g) ∧
      ∀ g : Fin m → ℕ, Fits l cap g → toLex g < toLex a →
        (∀ a' : Fin m → ℕ, Fits l cap a' → toLex a' < toLex a → toLex a' ≤ toLex g) →
          IsExtension (decrAt a (i.val + 1)) g (i.val + 1) := by
  set d := decrAt a (i.val + 1) with hd
  have hdi : d i = a i - 1 := by rw [hd, decrAt_apply]; simp
  have hdj : ∀ j : Fin m, j < i → d j = a j := by
    intro j hj
    rw [hd, decrAt_apply, if_neg]
    have : j.val < i.val := hj
    omega
  have hdfit : lam l d (i.val + 1) ≤ cap := by
    have h1 := decr_lam_le l hl a (i.val + 1) (i.val + 1)
    have h2 : lam l a (i.val + 1) ≤ lam l a m :=
      lam_mono l hl a (by have := i.isLt; omega)
    exact le_trans h1 (le_trans h2 hfit)
  obtain ⟨hext, hfit0, hmax0⟩ := greedy_core l hl cap d (i.val + 1) (by have := i.isLt; omega) hdfit
  set g0 := greedyFill l cap d (i.val + 1) with hg0
  have hg0j : ∀ j : Fin m, j < i → g0 j = a j := by
    intro j hj
    rw [hext j (by have : j.val < i.val := hj; omega), hdj j hj]
  have hg0i : g0 i = a i - 1 := by
    rw [hext i (by omega), hdi]
  have hlt0 : toLex g0 < toLex a := by
    apply lexlt' g0 a i hg0j
    rw [hg0i]; have := Nat.pos_of_ne_zero hi; omega
  have hmaximal : ∀ a' : Fin m → ℕ, Fits l cap a' → toLex a' < toLex a → toLex a' ≤ toLex g0 := by
    intro a' hfa' hlta'
    obtain ⟨k, hk1, hk2⟩ := (lexlt a' a).mp hlta'
    have hki : k ≤ i := by
      by_contra hcon
      have := hmax k (not_le.mp hcon)
      omega
    rcases lt_or_eq_of_le hki with hlt | heq
    · apply le_of_lt
      apply lexlt' a' g0 k
      · intro j hj; rw [hk1 j hj, hg0j j (lt_trans hj hlt)]
      · rw [hg0j k hlt]; exact hk2
    · subst heq
      by_cases hc : a' k = a k - 1
      · apply hmax0 a' _ hfa'
        intro j hj
        by_cases hji : j < k
        · rw [hk1 j hji, hdj j hji]
        · have : j = k := by
            apply le_antisymm
            · have : j.val < k.val + 1 := hj
              exact Fin.le_def.mpr (by omega)
            · exact not_lt.mp hji
          subst this; rw [hc, hdi]
      · apply le_of_lt
        apply lexlt' a' g0 k
        · intro j hj; rw [hk1 j hj, hg0j j hj]
        · rw [hg0i]; omega
  refine ⟨⟨g0, hfit0, hlt0, hmaximal⟩, ?_⟩
  intro g hg hgl hgm
  have h1 : toLex g0 ≤ toLex g := hgm g0 hfit0 hlt0
  have h2 : toLex g ≤ toLex g0 := hmaximal g hg hgl
  have : g = g0 := toLex.injective (le_antisymm h2 h1)
  rw [this]; exact hext


theorem lam_zero {m : ℕ} (l : Fin m → ℝ) (a : Fin m → ℕ) : lam l a 0 = 0 := by
  simp [lam]

theorem no_fit_of_neg {m : ℕ} (l : Fin m → ℝ) (hl : ∀ i, 0 < l i) (L : ℝ) (hL : L < 0)
    (a : Fin m → ℕ) : ¬ Fits l L a := by
  intro h
  have := lam_nonneg l hl a m
  have h' : lam l a m ≤ L := h
  linarith

def BadV {m : ℕ} (l b : Fin m → ℝ) (L0 M0 : ℝ) (a' : Fin m → ℕ) : Prop :=
  Fits l L0 a' ∧ M0 < bet b a' m

def BelowLt {m : ℕ} (a : Fin m → ℕ) (n : ℕ) (P : (Fin m → ℕ) → Prop) : Prop :=
  ∀ a', P a' → ∃ k : Fin m, k.val < n ∧ (∀ j, j < k → a' j = a j) ∧ a' k < a k

def rank : Phase → ℕ
  | .update => 3
  | .backtrack => 2
  | .step6 => 1
  | .test => 0
  | .done => 0

structure Good {m k : ℕ} (hk : 0 < k) (l b : Fin m → ℝ) (L c : Fin k → ℝ)
    (σ : State m k) : Prop where
  p1 : ∀ j : Fin k, c j ≤ σ.M j ∧
    (σ.M j = c j ∨ ∃ a : Fin m → ℕ, Fits l (L j) a ∧ bet b a m = σ.M j)
  fit : L ⟨0, hk⟩ < 0 ∨ Fits l (L ⟨0, hk⟩) σ.a
  inv : σ.phase = .test → ∃ i : Fin m, i.val + 1 = σ.s ∧ σ.a i ≠ 0
  upd : σ.phase = .update →
    (∀ a', BadV l b (L ⟨0, hk⟩) (σ.M ⟨0, hk⟩) a' → toLex a' ≤ toLex σ.a) ∧
    (0 < σ.t.val → ¬ BadV l b (L ⟨0, hk⟩) (σ.M ⟨0, hk⟩) σ.a)
  bt : σ.phase = .backtrack →
    ∀ a', BadV l b (L ⟨0, hk⟩) (σ.M ⟨0, hk⟩) a' → toLex a' < toLex σ.a
  tst : σ.phase = .test → BelowLt σ.a σ.s (BadV l b (L ⟨0, hk⟩) (σ.M ⟨0, hk⟩))
  s6 : σ.phase = .step6 → BelowLt σ.a (σ.s - 1) (BadV l b (L ⟨0, hk⟩) (σ.M ⟨0, hk⟩))
  dn : σ.phase = .done → ∀ a', Fits l (L ⟨0, hk⟩) a' → bet b a' m ≤ σ.M ⟨0, hk⟩

theorem key_fail {m k : ℕ} (hk : 0 < k) (l b : Fin m → ℝ) (hl : ∀ i, 0 < l i)
    (hb : ∀ i, 0 ≤ b i) (hdens : ∀ i i' : Fin m, i ≤ i' → b i' / l i' ≤ b i / l i)
    (L M : Fin k → ℝ) (a : Fin m → ℕ) (s : ℕ) (hs : 1 ≤ s) (hsm : s ≤ m)
    (hF : L ⟨0, hk⟩ < 0 ∨ Fits l (L ⟨0, hk⟩) a)
    (hn : ¬ TestHolds l b L M (decrAt a s) s ⟨0, hk⟩)
    (a' : Fin m → ℕ) (hpre : ∀ i : Fin m, i.val + 1 < s → a' i = a i)
    (hlast : ∀ i : Fin m, i.val + 1 = s → a' i < a i)
    (hfit : Fits l (L ⟨0, hk⟩) a') : bet b a' m ≤ M ⟨0, hk⟩ := by
  have hlam : lam l (decrAt a s) s ≤ L ⟨0, hk⟩ := by
    rcases hF with h | h
    · exact absurd hfit (no_fit_of_neg l hl _ h a')
    · exact le_trans (decr_lam_le l hl a s s) (le_trans (lam_mono l hl a hsm) h)
  have h2 : (L ⟨0, hk⟩ - lam l (decrAt a s) s) * nextB b s ≤
      (M ⟨0, hk⟩ - bet b (decrAt a s) s) * nextL l s := by
    unfold TestHolds at hn
    exact not_lt.mp (fun h => hn ⟨hlam, h⟩)
  refine successor_core l b hl hb hdens (L ⟨0, hk⟩) (M ⟨0, hk⟩) (decrAt a s) s hs hsm h2 a' ?_ ?_ hfit
  · intro i hi
    rw [decrAt_apply, if_neg (by omega)]
    exact hpre i hi
  · intro i hi
    rw [decrAt_apply, if_pos hi]
    have := hlast i hi
    omega

theorem greedy_lt {m : ℕ} (l : Fin m → ℝ) (cap : ℝ) (a : Fin m → ℕ) (s : ℕ) (hl : ∀ i, 0 < l i)
    (i : Fin m) (his : i.val + 1 = s) (hai : a i ≠ 0) :
    toLex (greedyFill l cap (decrAt a s) s) < toLex a := by
  obtain ⟨hc1, _⟩ := greedy_char l hl cap (decrAt a s) s
  apply lexlt' _ _ i
  · intro j hj
    have : j.val < i.val := hj
    rw [hc1 j (by omega), decrAt_apply, if_neg (by omega)]
  · rw [hc1 i (by omega), decrAt_apply, if_pos his]
    have := Nat.pos_of_ne_zero hai
    omega

theorem decr_lt {m : ℕ} (a : Fin m → ℕ) (s : ℕ)
    (i : Fin m) (his : i.val + 1 = s) (hai : a i ≠ 0) :
    toLex (decrAt a s) < toLex a := by
  apply lexlt' _ _ i
  · intro j hj
    have : j.val < i.val := hj
    rw [decrAt_apply, if_neg (by omega)]
  · rw [decrAt_apply, if_pos his]
    have := Nat.pos_of_ne_zero hai
    omega


theorem good_step {m k : ℕ} (hk : 0 < k) (l b : Fin m → ℝ) (L c : Fin k → ℝ)
    (hl : ∀ i, 0 < l i) (hb : ∀ i, 0 ≤ b i)
    (hdens : ∀ i i' : Fin m, i ≤ i' → b i' / l i' ≤ b i / l i) (hL : StrictAnti L)
    (σ τ : State m k) (hG : Good hk l b L c σ) (hst : Step l b L c σ τ) :
    Good hk l b L c τ := by
  have hL0 : ∀ j : Fin k, L j ≤ L ⟨0, hk⟩ := fun j =>
    hL.antitone (Fin.le_def.mpr (Nat.zero_le _))
  cases hst with
  | update a s t M =>
    obtain ⟨hu1, hu2⟩ := hG.upd rfl
    dsimp only at hu1 hu2
    have hM'ge : M ⟨0, hk⟩ ≤ (if t ≤ ⟨0, hk⟩ ∧ Fits l (L ⟨0, hk⟩) a ∧ M ⟨0, hk⟩ < bet b a m
        then bet b a m else M ⟨0, hk⟩) := by
      split_ifs with hc
      · exact hc.2.2.le
      · exact le_rfl
    refine ⟨?_, hG.fit, (fun h => nomatch h), (fun h => nomatch h), ?_, (fun h => nomatch h), (fun h => nomatch h), (fun h => nomatch h)⟩
    · intro j
      have h1 := hG.p1 j
      dsimp only at h1 ⊢
      split_ifs with hc
      · exact ⟨le_trans h1.1 hc.2.2.le, Or.inr ⟨a, hc.2.1, rfl⟩⟩
      · exact h1
    · intro _ a' hbad
      dsimp only at hbad ⊢
      have hbad0 : BadV l b (L ⟨0, hk⟩) (M ⟨0, hk⟩) a' := ⟨hbad.1, lt_of_le_of_lt hM'ge hbad.2⟩
      have hle := hu1 a' hbad0
      refine lt_of_le_of_ne hle (fun e => ?_)
      have e' : a' = a := toLex.injective e
      subst e'
      obtain ⟨hf, hlt⟩ := hbad
      by_cases ht : t.val = 0
      · have htl : t ≤ ⟨0, hk⟩ := Fin.le_def.mpr (by omega)
        by_cases hc : M ⟨0, hk⟩ < bet b a' m
        · rw [if_pos ⟨htl, hf, hc⟩] at hlt
          exact lt_irrefl _ hlt
        · rw [if_neg (fun h => hc h.2.2)] at hlt
          exact hc hlt
      · have htl : ¬ t ≤ ⟨0, hk⟩ := fun h => ht (by have := Fin.le_def.mp h; simp at this; exact this)
        rw [if_neg (fun h => htl h.1)] at hlt
        exact hu2 (by omega) ⟨hf, hlt⟩
  | backtrack_found a s t M i hi hmax =>
    have hb' := hG.bt rfl
    dsimp only at hb'
    refine ⟨hG.p1, hG.fit, fun _ => ⟨i, rfl, hi⟩, (fun h => nomatch h), (fun h => nomatch h), ?_, (fun h => nomatch h), (fun h => nomatch h)⟩
    intro _ a' hbad
    obtain ⟨k', hk1, hk2⟩ := (lexlt a' a).mp (hb' a' hbad)
    refine ⟨k', ?_, hk1, hk2⟩
    have : k' ≤ i := by
      by_contra hcon
      have := hmax k' (not_le.mp hcon)
      omega
    have := Fin.le_def.mp this
    show k'.val < i.val + 1
    omega
  | backtrack_zero a s t M h0 =>
    have hb' := hG.bt rfl
    dsimp only at hb'
    refine ⟨hG.p1, hG.fit, (fun h => nomatch h), (fun h => nomatch h), (fun h => nomatch h), (fun h => nomatch h), (fun h => nomatch h), ?_⟩
    intro _ a' hfit
    by_contra hcon
    have := hb' a' ⟨hfit, not_le.mp hcon⟩
    obtain ⟨k', hk1, hk2⟩ := (lexlt a' a).mp this
    have := h0 k'
    omega
  | test_pass a s t M hs hsm t' ht' hmin =>
    have hinv := hG.inv rfl
    have htst := hG.tst rfl
    dsimp only at hinv htst
    obtain ⟨i0, hi0, hai0⟩ := hinv
    obtain ⟨hext, hfitG, hmaxG⟩ := greedy_core l hl (L t') (decrAt a s) s hsm ht'.1
    have hfitG0 : Fits l (L ⟨0, hk⟩) (greedyFill l (L t') (decrAt a s) s) :=
      le_trans hfitG (hL0 t')
    -- t' > 0 : test fails at index 0
    have hfail0 : 0 < t'.val → ¬ TestHolds l b L M (decrAt a s) s ⟨0, hk⟩ := by
      intro ht0 hh
      have : t'.val ≤ 0 := Fin.le_def.mp (hmin _ hh)
      omega
    refine ⟨hG.p1, Or.inr hfitG0, (fun h => nomatch h), ?_, (fun h => nomatch h), (fun h => nomatch h), (fun h => nomatch h), (fun h => nomatch h)⟩
    intro _
    dsimp only
    have hFa := hG.fit
    constructor
    · intro a' hbad
      obtain ⟨k', hk1, hk2, hk3⟩ := htst a' hbad
      by_cases hlt : k'.val + 1 < s
      · apply le_of_lt
        apply lexlt' a' _ k'
        · intro j hj
          rw [hk2 j hj, hext j (by have : j.val < k'.val := hj; omega), decrAt_apply, if_neg (by
            have : j.val < k'.val := hj; omega)]
        · rw [hext k' (by omega), decrAt_apply, if_neg (by omega)]
          exact hk3
      · have hks : k'.val + 1 = s := by omega
        by_cases ht0 : t'.val = 0
        · have ht'0 : t' = ⟨0, hk⟩ := Fin.ext ht0
          subst ht'0
          by_cases hc : a' k' < decrAt a s k'
          · apply le_of_lt
            apply lexlt' a' _ k'
            · intro j hj
              rw [hk2 j hj, hext j (by have : j.val < k'.val := hj; omega), decrAt_apply,
                if_neg (by have : j.val < k'.val := hj; omega)]
            · rw [hext k' (by omega)]; exact hc
          · apply hmaxG a' _ hbad.1
            intro j hj
            by_cases hjk : j < k'
            · rw [hk2 j hjk, decrAt_apply, if_neg (by have : j.val < k'.val := hjk; omega)]
            · have hjk' : j = k' := by
                apply le_antisymm
                · exact Fin.le_def.mpr (by have : j.val < s := hj; omega)
                · exact not_lt.mp hjk
              subst hjk'
              have h1 := hk3
              rw [decrAt_apply, if_pos hks] at hc
              rw [decrAt_apply, if_pos hks]
              omega
        · exfalso
          have := key_fail hk l b hl hb hdens L M a s (by omega) hsm hFa (hfail0 (by omega)) a'
            (fun i hi => hk2 i (by
              show i.val < k'.val
              omega)) (fun i hi => by
              have : i = k' := Fin.ext (by omega)
              subst this; exact hk3) hbad.1
          exact absurd hbad.2 (not_lt.mpr this)
    · intro ht0 hbad
      have := key_fail hk l b hl hb hdens L M a s (by omega) hsm hFa (hfail0 ht0)
        (greedyFill l (L t') (decrAt a s) s)
        (fun i hi => by rw [hext i (by omega), decrAt_apply, if_neg (by omega)])
        (fun i hi => by
          rw [hext i (by omega), decrAt_apply, if_pos hi]
          have : i = i0 := Fin.ext (by omega)
          subst this
          have := Nat.pos_of_ne_zero hai0
          omega) hfitG0
      exact absurd hbad.2 (not_lt.mpr this)
  | test_fail a s t M hs hsm hnone =>
    have hinv := hG.inv rfl
    have htst := hG.tst rfl
    dsimp only at hinv htst
    obtain ⟨i0, hi0, hai0⟩ := hinv
    refine ⟨hG.p1, ?_, (fun h => nomatch h), (fun h => nomatch h), (fun h => nomatch h), (fun h => nomatch h), ?_, (fun h => nomatch h)⟩
    · rcases hG.fit with h | h
      · exact Or.inl h
      · exact Or.inr (le_trans (decr_lam_le l hl a s m) h)
    · intro _ a' hbad
      dsimp only
      obtain ⟨k', hk1, hk2, hk3⟩ := htst a' hbad
      by_cases hlt : k'.val + 1 < s
      · refine ⟨k', by omega, ?_, ?_⟩
        · intro j hj
          rw [hk2 j hj, decrAt_apply, if_neg (by have : j.val < k'.val := hj; omega)]
        · rw [decrAt_apply, if_neg (by omega)]; exact hk3
      · exfalso
        have := key_fail hk l b hl hb hdens L M a s (by omega) hsm hG.fit (hnone ⟨0, hk⟩) a'
          (fun i hi => hk2 i (by
            show i.val < k'.val
            omega)) (fun i hi => by
            have : i = k' := Fin.ext (by omega)
            subst this; exact hk3) hbad.1
        exact absurd hbad.2 (not_lt.mpr this)
  | step6_found a s t M i hi hai hmax =>
    have hs6 := hG.s6 rfl
    dsimp only at hs6
    refine ⟨hG.p1, hG.fit, fun _ => ⟨i, rfl, hai⟩, (fun h => nomatch h), (fun h => nomatch h), ?_, (fun h => nomatch h), (fun h => nomatch h)⟩
    intro _ a' hbad
    obtain ⟨k', hk1, hk2, hk3⟩ := hs6 a' hbad
    refine ⟨k', ?_, hk2, hk3⟩
    have : k' ≤ i := by
      by_contra hcon
      have := hmax k' (not_le.mp hcon) (by omega)
      omega
    have := Fin.le_def.mp this
    show k'.val < i.val + 1
    omega
  | step6_none a s t M hnone =>
    have hs6 := hG.s6 rfl
    dsimp only at hs6
    refine ⟨hG.p1, hG.fit, (fun h => nomatch h), (fun h => nomatch h), (fun h => nomatch h), (fun h => nomatch h), (fun h => nomatch h), ?_⟩
    intro _ a' hfit
    by_contra hcon
    obtain ⟨k', hk1, hk2, hk3⟩ := hs6 a' ⟨hfit, not_le.mp hcon⟩
    have := hnone k' (by omega)
    omega


theorem good_start {m k : ℕ} (hk : 0 < k) (l b : Fin m → ℝ) (L c : Fin k → ℝ)
    (hl : ∀ i, 0 < l i) : Good hk l b L c (start l L c hk) := by
  have hs : start l L c hk = ⟨greedyFill l (L ⟨0, hk⟩) 0 0, 0, ⟨0, hk⟩, c, .update⟩ := rfl
  rw [hs]
  have hfit : 0 ≤ L ⟨0, hk⟩ → Fits l (L ⟨0, hk⟩) (greedyFill l (L ⟨0, hk⟩) 0 0) := by
    intro h
    exact (greedy_core l hl (L ⟨0, hk⟩) 0 0 (Nat.zero_le _) (by rw [lam_zero]; exact h)).2.1
  refine ⟨fun j => ⟨le_rfl, Or.inl rfl⟩, ?_, (fun h => nomatch h), ?_, (fun h => nomatch h),
    (fun h => nomatch h), (fun h => nomatch h), (fun h => nomatch h)⟩
  · by_cases h : 0 ≤ L ⟨0, hk⟩
    · exact Or.inr (hfit h)
    · exact Or.inl (not_le.mp h)
  · intro _
    refine ⟨?_, fun h => absurd h (by simp)⟩
    intro a' hbad
    have h0 : 0 ≤ L ⟨0, hk⟩ := by
      by_contra h
      exact no_fit_of_neg l hl _ (not_le.mp h) a' hbad.1
    exact (greedy_core l hl (L ⟨0, hk⟩) 0 0 (Nat.zero_le _) (by rw [lam_zero]; exact h0)).2.2 a'
      (fun i hi => absurd hi (by omega)) hbad.1

theorem good_reach {m k : ℕ} (hk : 0 < k) (l b : Fin m → ℝ) (L c : Fin k → ℝ)
    (hl : ∀ i, 0 < l i) (hb : ∀ i, 0 ≤ b i)
    (hdens : ∀ i i' : Fin m, i ≤ i' → b i' / l i' ≤ b i / l i) (hL : StrictAnti L)
    (σ : State m k) (hσ : Reachable l b L c hk σ) : Good hk l b L c σ := by
  induction hσ with
  | refl => exact good_start hk l b L c hl
  | tail _ hst ih => exact good_step hk l b L c hl hb hdens hL _ _ ih hst


def Inv0 {m k : ℕ} (σ : State m k) : Prop :=
  σ.phase = .test → ∃ i : Fin m, i.val + 1 = σ.s ∧ σ.a i ≠ 0

theorem inv0_step {m k : ℕ} (l b : Fin m → ℝ) (L c : Fin k → ℝ)
    (σ τ : State m k) (hI : Inv0 σ) (hst : Step l b L c σ τ) : Inv0 τ := by
  cases hst with
  | update a s t M => exact fun h => nomatch h
  | backtrack_found a s t M i hi hmax => exact fun _ => ⟨i, rfl, hi⟩
  | backtrack_zero a s t M h0 => exact fun h => nomatch h
  | test_pass a s t M hs hsm t' ht' hmin => exact fun h => nomatch h
  | test_fail a s t M hs hsm hnone => exact fun h => nomatch h
  | step6_found a s t M i hi hai hmax => exact fun _ => ⟨i, rfl, hai⟩
  | step6_none a s t M hnone => exact fun h => nomatch h

theorem inv0_reach {m k : ℕ} (hk : 0 < k) (l b : Fin m → ℝ) (L c : Fin k → ℝ)
    (σ : State m k) (hσ : Reachable l b L c hk σ) : Inv0 σ := by
  induction hσ with
  | refl => exact fun h => nomatch h
  | tail _ hst ih => exact inv0_step l b L c _ _ ih hst

theorem step_cases {m k : ℕ} (l b : Fin m → ℝ) (L c : Fin k → ℝ)
    (hl : ∀ i, 0 < l i)
    (σ τ : State m k) (hI : Inv0 σ) (hst : Step l b L c σ τ) :
    toLex τ.a < toLex σ.a ∨ (τ.a = σ.a ∧ rank τ.phase < rank σ.phase) := by
  cases hst with
  | update a s t M => exact Or.inr ⟨rfl, by simp [rank]⟩
  | backtrack_found a s t M i hi hmax => exact Or.inr ⟨rfl, by simp [rank]⟩
  | backtrack_zero a s t M h0 => exact Or.inr ⟨rfl, by simp [rank]⟩
  | test_pass a s t M hs hsm t' ht' hmin =>
    obtain ⟨i0, hi0, hai0⟩ := hI rfl
    exact Or.inl (greedy_lt l (L t') a s hl i0 hi0 hai0)
  | test_fail a s t M hs hsm hnone =>
    obtain ⟨i0, hi0, hai0⟩ := hI rfl
    exact Or.inl (decr_lt a s i0 hi0 hai0)
  | step6_found a s t M i hi hai hmax => exact Or.inr ⟨rfl, by simp [rank]⟩
  | step6_none a s t M hnone => exact Or.inr ⟨rfl, by simp [rank]⟩

theorem tvi_core {m k : ℕ} (hk : 0 < k) (l b : Fin m → ℝ) (L c : Fin k → ℝ)
    (hl : ∀ i, 0 < l i) (hb : ∀ i, 0 ≤ b i)
    (hdens : ∀ i i' : Fin m, i ≤ i' → b i' / l i' ≤ b i / l i) (hL : StrictAnti L)
    (σ : State m k) (hσ : Reachable l b L c hk σ) (hu : σ.phase = .update) :
    (∀ j : Fin k, c j ≤ σ.M j ∧
        (σ.M j = c j ∨ ∃ a : Fin m → ℕ, Fits l (L j) a ∧ bet b a m = σ.M j)) ∧
      ∀ a' : Fin m → ℕ, toLex σ.a < toLex a' → Fits l (L ⟨0, hk⟩) a' →
        bet b a' m ≤ σ.M ⟨0, hk⟩ := by
  have hG := good_reach hk l b L c hl hb hdens hL σ hσ
  refine ⟨hG.p1, fun a' hlt hf => ?_⟩
  by_contra hcon
  have := (hG.upd hu).1 a' ⟨hf, not_le.mp hcon⟩
  exact absurd hlt (not_lt.mpr this)

theorem reach_le {m k : ℕ} (hk : 0 < k) (l b : Fin m → ℝ) (L c : Fin k → ℝ)
    (hl : ∀ i, 0 < l i)
    (σ τ : State m k) (hσ : Reachable l b L c hk σ)
    (h : Relation.ReflTransGen (Step l b L c) σ τ) : toLex τ.a ≤ toLex σ.a := by
  induction h with
  | refl => exact le_rfl
  | tail hρ hst ih =>
    rename_i ρ τ'
    have hGρ := inv0_reach hk l b L c ρ (hσ.trans hρ)
    rcases step_cases l b L c hl ρ τ' hGρ hst with h1 | ⟨h1, _⟩
    · exact le_trans h1.le ih
    · rw [h1]; exact ih

theorem tvd_core {m k : ℕ} (hk : 0 < k) (l b : Fin m → ℝ) (L c : Fin k → ℝ)
    (hl : ∀ i, 0 < l i) (hL : StrictAnti L)
    (σ σ' : State m k)
    (hσ : Reachable l b L c hk σ) (hu : σ.phase = .update)
    (hσσ' : Relation.TransGen (Step l b L c) σ σ') (hu' : σ'.phase = .update) :
    toLex σ'.a < toLex σ.a ∧ Fits l (L ⟨0, hk⟩) σ'.a := by
  have hL0 : ∀ j : Fin k, L j ≤ L ⟨0, hk⟩ := fun j =>
    hL.antitone (Fin.le_def.mpr (Nat.zero_le _))
  obtain ⟨τ, hτ, hst⟩ := Relation.TransGen.tail'_iff.mp hσσ'
  have hGτ := inv0_reach hk l b L c τ (hσ.trans hτ)
  have hle := reach_le hk l b L c hl σ τ hσ hτ
  cases hst with
  | test_pass a s t M hs hsm t'' ht' hmin =>
    obtain ⟨i0, hi0, hai0⟩ := hGτ rfl
    refine ⟨lt_of_lt_of_le (greedy_lt l (L t'') a s hl i0 hi0 hai0) hle, ?_⟩
    exact le_trans (greedy_core l hl (L t'') (decrAt a s) s hsm ht'.1).2.1 (hL0 t'')
  | update a s t M => cases hu'
  | backtrack_found a s t M i hi hmax => cases hu'
  | backtrack_zero a s t M h0 => cases hu'
  | test_fail a s t M hs hsm hnone => cases hu'
  | step6_found a s t M i hi hai hmax => cases hu'
  | step6_none a s t M hnone => cases hu'

theorem goal_core {m k : ℕ} (hk : 0 < k) (l b : Fin m → ℝ)
    (L c : Fin k → ℝ) (hl : ∀ i, 0 < l i) (hb : ∀ i, 0 ≤ b i)
    (hdens : ∀ i i' : Fin m, i ≤ i' → b i' / l i' ≤ b i / l i) (hL : StrictAnti L) :
    (∀ σ : State m k, Reachable l b L c hk σ → Acc (fun x y => Step l b L c y x) σ) ∧
      (∀ σ : State m k, Reachable l b L c hk σ → σ.phase ≠ .done →
        ∃ σ' : State m k, Step l b L c σ σ') ∧
      (∀ σ : State m k, Reachable l b L c hk σ → σ.phase = .done →
        (∀ j : Fin k, c j ≤ σ.M j ∧
            (σ.M j = c j ∨ ∃ a : Fin m → ℕ, Fits l (L j) a ∧ bet b a m = σ.M j)) ∧
          IsKnapsackMax l b (L ⟨0, hk⟩) (c ⟨0, hk⟩) (σ.M ⟨0, hk⟩)) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · -- termination
    let μ : State m k → Prod (Lex (Fin m → ℕ)) ℕ := fun σ => (toLex σ.a, rank σ.phase)
    have wf : WellFounded (fun τ σ : State m k =>
        Prod.Lex (· < ·) (· < ·) (μ τ) (μ σ)) :=
      InvImage.wf μ (WellFounded.prod_lex wellFounded_lt wellFounded_lt)
    intro σ
    refine wf.induction (C := fun σ => Reachable l b L c hk σ → Acc (fun x y => Step l b L c y x) σ)
      σ ?_
    intro σ ih hσ
    apply Acc.intro
    intro τ hst
    refine ih τ ?_ (hσ.tail hst)
    have hG := good_reach hk l b L c hl hb hdens hL σ hσ
    rcases step_cases l b L c hl σ τ hG.inv hst with h1 | ⟨h1, h2⟩
    · exact Prod.Lex.left _ _ h1
    · show Prod.Lex _ _ (toLex τ.a, rank τ.phase) (toLex σ.a, rank σ.phase)
      rw [h1]
      exact Prod.Lex.right _ h2
  · intro σ hσ hnd
    have hG := good_reach hk l b L c hl hb hdens hL σ hσ
    obtain ⟨a, s, t, M, ph⟩ := σ
    cases ph with
    | update => exact ⟨_, Step.update a s t M⟩
    | done => exact absurd rfl hnd
    | backtrack =>
      by_cases h0 : ∀ i : Fin m, a i = 0
      · exact ⟨_, Step.backtrack_zero a s t M h0⟩
      · push_neg at h0
        obtain ⟨i1, hi1⟩ := h0
        have hne : (Finset.univ.filter (fun i : Fin m => a i ≠ 0)).Nonempty :=
          ⟨i1, by simp [hi1]⟩
        set i := (Finset.univ.filter (fun i : Fin m => a i ≠ 0)).max' hne with hi
        have hmem : i ∈ Finset.univ.filter (fun i : Fin m => a i ≠ 0) := Finset.max'_mem _ _
        refine ⟨_, Step.backtrack_found a s t M i (by simpa using hmem) ?_⟩
        intro i' hi'
        by_contra hcon
        have : i' ∈ Finset.univ.filter (fun i : Fin m => a i ≠ 0) := by simpa using hcon
        have := Finset.le_max' _ i' this
        exact absurd hi' (not_lt.mpr this)
    | test =>
      obtain ⟨i0, hi0, hai0⟩ := hG.inv rfl
      dsimp only at hi0
      have hs : 0 < s := by omega
      have hsm : s ≤ m := by have := i0.isLt; omega
      by_cases hex : ∃ j : Fin k, TestHolds l b L M (decrAt a s) s j
      · have hne : (Finset.univ.filter (fun j : Fin k => TestHolds l b L M (decrAt a s) s j)).Nonempty := by
          obtain ⟨j, hj⟩ := hex
          exact ⟨j, by simpa using hj⟩
        set t' := (Finset.univ.filter (fun j : Fin k => TestHolds l b L M (decrAt a s) s j)).min' hne
          with ht'
        have hmem : t' ∈ Finset.univ.filter (fun j : Fin k => TestHolds l b L M (decrAt a s) s j) :=
          Finset.min'_mem _ _
        refine ⟨_, Step.test_pass a s t M hs hsm t' (by simpa using hmem) ?_⟩
        intro j hj
        exact Finset.min'_le _ j (by simpa using hj)
      · push_neg at hex
        exact ⟨_, Step.test_fail a s t M hs hsm hex⟩
    | step6 =>
      by_cases hex : ∃ i : Fin m, i.val + 1 ≤ s - 1 ∧ a i ≠ 0
      · have hne : (Finset.univ.filter (fun i : Fin m => i.val + 1 ≤ s - 1 ∧ a i ≠ 0)).Nonempty := by
          obtain ⟨j, hj⟩ := hex
          exact ⟨j, by simpa using hj⟩
        set i := (Finset.univ.filter (fun i : Fin m => i.val + 1 ≤ s - 1 ∧ a i ≠ 0)).max' hne with hi
        have hmem : i ∈ Finset.univ.filter (fun i : Fin m => i.val + 1 ≤ s - 1 ∧ a i ≠ 0) :=
          Finset.max'_mem _ _
        have hmem' : i.val + 1 ≤ s - 1 ∧ a i ≠ 0 := by simpa using hmem
        refine ⟨_, Step.step6_found a s t M i hmem'.1 hmem'.2 ?_⟩
        intro i' hi' hi's
        by_contra hcon
        have : i' ∈ Finset.univ.filter (fun i : Fin m => i.val + 1 ≤ s - 1 ∧ a i ≠ 0) := by
          simpa using ⟨hi's, hcon⟩
        have := Finset.le_max' _ i' this
        exact absurd hi' (not_lt.mpr this)
      · push_neg at hex
        exact ⟨_, Step.step6_none a s t M hex⟩
  · intro σ hσ hd
    have hG := good_reach hk l b L c hl hb hdens hL σ hσ
    have h1 := hG.p1 ⟨0, hk⟩
    exact ⟨hG.p1, h1.1, hG.dn hd, h1.2⟩

end CuttingStock63.Knapsack

open CuttingStock63.Knapsack


theorem solution {m k : ℕ} (hk : 0 < k) (l b : Fin m → ℝ) (L c : Fin k → ℝ)
    (hl : ∀ i, 0 < l i) (hb : ∀ i, 0 ≤ b i)
    (hdens : ∀ i i' : Fin m, i ≤ i' → b i' / l i' ≤ b i / l i) (hL : StrictAnti L)
    (σ : State m k) (hσ : Reachable l b L c hk σ) (hu : σ.phase = .update) :
    (∀ j : Fin k, c j ≤ σ.M j ∧
        (σ.M j = c j ∨ ∃ a : Fin m → ℕ, Fits l (L j) a ∧ bet b a m = σ.M j)) ∧
      ∀ a' : Fin m → ℕ, toLex σ.a < toLex a' → Fits l (L ⟨0, hk⟩) a' →
        bet b a' m ≤ σ.M ⟨0, hk⟩ := by
  exact tvi_core hk l b L c hl hb hdens hL σ hσ hu
