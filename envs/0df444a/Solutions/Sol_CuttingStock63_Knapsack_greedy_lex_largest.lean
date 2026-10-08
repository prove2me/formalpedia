-- Prove2me | solution 1 for CuttingStock63.Knapsack.greedy_lex_largest
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T14:55:14.059785+00:00
-- url     : https://prove2.me/submissions/b6d5793d-c6c6-42be-a40b-dbc86ba7a648

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

end CuttingStock63.Knapsack

open CuttingStock63.Knapsack


theorem solution {m : ℕ} (l : Fin m → ℝ) (hl : ∀ i, 0 < l i) (cap : ℝ)
    (a : Fin m → ℕ) (s : ℕ) (hs : s ≤ m) (hfit : lam l a s ≤ cap) :
    IsExtension a (greedyFill l cap a s) s ∧ Fits l cap (greedyFill l cap a s) ∧
      ∀ a' : Fin m → ℕ, IsExtension a a' s → Fits l cap a' →
        toLex a' ≤ toLex (greedyFill l cap a s) := by
  exact greedy_core l hl cap a s hs hfit
