-- Prove2me | solution 1 for EndogBudgetAds.Equilibrium.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T16:33:45.27992+00:00
-- url     : https://prove2.me/submissions/ef39f81a-39fa-4376-aa20-4a5320be1c7d

import Mathlib
import Definitions.Def_EndogBudgetAds_Equilibrium_Model
import Definitions.Def_EndogBudgetAds_Equilibrium_Proof
open MeasureTheory

namespace EndogLemma2Aux
open EndogBudgetAds.Equilibrium

lemma le_top2_of_top {m : ℕ} {x : Fin m → ℝ} {k l : Fin m}
    (hk : EndogBudgetAds.Equilibrium.IsTop x k) (hl : l ≠ k) : x l ≤ top2 x := by
  unfold top2
  have hmem : (l, k) ∈ (Finset.univ.filter fun p : Fin m × Fin m => p.1 ≠ p.2) := by
    simp [hl]
  rw [dif_pos ⟨_, hmem⟩]
  refine le_trans ?_ (Finset.le_sup' (fun p => min (x p.1) (x p.2)) hmem)
  simp only
  rw [min_eq_left (le_of_lt (hk l hl))]

lemma top2_nonneg_pos {m : ℕ} (x : Fin m → ℝ) (hx : ∀ l, 0 < x l) : 0 ≤ top2 x := by
  unfold top2
  split_ifs with h
  · obtain ⟨p, hp⟩ := h
    exact le_trans (le_min (hx p.1).le (hx p.2).le)
      (Finset.le_sup' (fun p => min (x p.1) (x p.2)) hp)
  · exact le_rfl

lemma top2Excl_le_top2 {m : ℕ} (x : Fin m → ℝ) (j : Fin m) (hx : ∀ l, 0 < x l) :
    top2Excl x j ≤ top2 x := by
  unfold top2Excl
  split_ifs with h
  · apply Finset.sup'_le
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    have hmem : p ∈ (Finset.univ.filter fun p : Fin m × Fin m => p.1 ≠ p.2) := by
      simp [hp.1]
    unfold top2
    rw [dif_pos ⟨_, hmem⟩]
    exact Finset.le_sup' (fun p => min (x p.1) (x p.2)) hmem
  · exact top2_nonneg_pos x hx

lemma pay_le_of {m n : ℕ} (b : Fin m → Fin n → ℝ) (i : Fin n) (k : Fin m) (c : ℝ)
    (hex : ∃ l, b l i < b k i) (h : ∀ l, l ≠ k → b l i ≤ b k i → b l i ≤ c) :
    pay b i k ≤ c := by
  unfold pay
  rw [dif_pos hex]
  apply Finset.sup'_le
  intro l hl
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
  exact h l hl.1 hl.2

/-- The per-item inequality behind Lemma 2. -/
lemma per_item {m n : ℕ} (w b : Fin m → Fin n → ℝ) (i : Fin n) (j k : Fin m) (hkj : k ≠ j)
    (hbw : ∀ l, l ≠ j → b l i = w l i) (hpos : ∀ l, 0 < w l i)
    (hw : ∀ a c, a ≠ c → w a i ≠ w c i) (hb : ∀ a c, a ≠ c → b a i ≠ b c i) :
    (if EndogBudgetAds.Equilibrium.IsTop (fun l => b l i) k then pay b i k else 0) ≤
      (if EndogBudgetAds.Equilibrium.IsTop (fun l => w l i) k then top2 (fun l => w l i) else 0)
      + (if EndogBudgetAds.Equilibrium.IsTop (fun l => w l i) k ∧
          IsSecond (fun l => b l i) j then b j i - top2 (fun l => w l i) else 0)
      - (if EndogBudgetAds.Equilibrium.IsTop (fun l => w l i) k ∧
          EndogBudgetAds.Equilibrium.IsTop (fun l => b l i) j then
          top2Excl (fun l => w l i) j else 0)
      + (if EndogBudgetAds.Equilibrium.IsTop (fun l => w l i) j ∧
          IsSecond (fun l => w l i) k then top2 (fun l => w l i) else 0) := by
  set x : Fin m → ℝ := fun l => w l i with hx
  set y : Fin m → ℝ := fun l => b l i with hy
  have hxpos : ∀ l, 0 < x l := hpos
  have hX3 : 0 ≤ (if EndogBudgetAds.Equilibrium.IsTop x j ∧ IsSecond x k then top2 x else 0) := by
    split_ifs
    · exact top2_nonneg_pos x hxpos
    · exact le_rfl
  have hbk : b k i = w k i := hbw k hkj
  by_cases hBk : EndogBudgetAds.Equilibrium.IsTop y k
  · rw [if_pos hBk]
    have hnBj : ¬ EndogBudgetAds.Equilibrium.IsTop y j := fun h =>
      lt_asymm (h k hkj) (hBk j hkj.symm)
    have hex : ∃ l, b l i < b k i := ⟨j, hBk j hkj.symm⟩
    have hX2 : (if EndogBudgetAds.Equilibrium.IsTop x k ∧
        EndogBudgetAds.Equilibrium.IsTop y j then top2Excl x j else 0) = 0 :=
      if_neg fun h => hnBj h.2
    rw [hX2]
    by_cases hWk : EndogBudgetAds.Equilibrium.IsTop x k
    · rw [if_pos hWk]
      by_cases hSj : IsSecond y j
      · rw [if_pos ⟨hWk, hSj⟩]
        have : pay b i k ≤ b j i := by
          refine pay_le_of b i k _ hex fun l hlk hle => ?_
          by_cases hlj : l = j
          · rw [hlj]
          · obtain ⟨l0, _, hlt, hall⟩ := hSj
            by_cases hl0 : l = l0
            · exfalso
              have hk' : b k i < b j i := by
                by_cases hk0 : k = l0
                · exfalso; rw [← hk0] at hl0; exact hlk hl0
                · exact hall k hk0 hkj
              rw [hl0] at hle
              change b l0 i ≤ b k i at hle
              linarith
            · exact le_of_lt (hall l hl0 hlj)
        linarith
      · rw [if_neg fun h => hSj h.2]
        have : pay b i k ≤ top2 x := by
          refine pay_le_of b i k _ hex fun l hlk hle => ?_
          by_cases hlj : l = j
          · -- someone other than j, k bids above j
            have : ∃ l', l' ≠ k ∧ l' ≠ j ∧ b j i ≤ b l' i := by
              by_contra hcon
              push_neg at hcon
              exact hSj ⟨k, hkj, hBk j hkj.symm, fun l' h1 h2 => hcon l' h1 h2⟩
            obtain ⟨l', h1, h2, h3⟩ := this
            rw [hlj]
            have := le_top2_of_top hWk h1
            rw [hbw l' h2] at h3
            exact le_trans h3 this
          · rw [hbw l hlj]; exact le_top2_of_top hWk hlk
        linarith
    · rw [if_neg hWk, if_neg fun h => hWk h.1]
      -- j is the top of `w`, k the second
      have hjk : w k i < w j i := by
        by_contra hcon
        push_neg at hcon
        apply hWk
        intro l hl
        by_cases hlj : l = j
        · rw [hlj]; exact lt_of_le_of_ne hcon (hw j k hkj.symm)
        · show w l i < w k i
          rw [← hbw l hlj, ← hbk]; exact hBk l hl
      have hothers : ∀ l, l ≠ j → l ≠ k → w l i < w k i := fun l hlj hlk => by
        rw [← hbw l hlj, ← hbk]; exact hBk l hlk
      have hWj : EndogBudgetAds.Equilibrium.IsTop x j := fun l hl => by
        by_cases hlk : l = k
        · rw [hlk]; exact hjk
        · exact lt_trans (hothers l hl hlk) hjk
      have hSk : IsSecond x k := ⟨j, hkj.symm, hjk, fun l h1 h2 => hothers l h1 h2⟩
      rw [if_pos ⟨hWj, hSk⟩]
      have : pay b i k ≤ top2 x := by
        refine pay_le_of b i k _ hex fun l _ hle => ?_
        refine le_trans hle ?_
        rw [hbk]; exact le_top2_of_top hWj hkj
      linarith
  · rw [if_neg hBk]
    have hX1 : (if EndogBudgetAds.Equilibrium.IsTop x k ∧ IsSecond y j then
        b j i - top2 x else 0) = 0 := by
      refine if_neg fun ⟨hWk, hSj⟩ => ?_
      obtain ⟨l0, hl0j, hlt, hall⟩ := hSj
      by_cases hl0k : l0 = k
      · apply hBk
        intro l hl
        by_cases hlj : l = j
        · rw [hlj, ← hl0k]; exact hlt
        · rw [← hl0k] at hl ⊢
          exact lt_trans (hall l hl hlj) hlt
      · have h1 : b k i < b j i := hall k (Ne.symm hl0k) hkj
        have h2 : w l0 i < w k i := hWk l0 hl0k
        change b j i < b l0 i at hlt
        rw [hbw l0 hl0j] at hlt
        rw [hbk] at h1
        linarith
    rw [hX1]
    have hPX2 : 0 ≤ (if EndogBudgetAds.Equilibrium.IsTop x k then top2 x else 0) -
        (if EndogBudgetAds.Equilibrium.IsTop x k ∧
          EndogBudgetAds.Equilibrium.IsTop y j then top2Excl x j else 0) := by
      by_cases hWk : EndogBudgetAds.Equilibrium.IsTop x k
      · rw [if_pos hWk]
        split_ifs
        · linarith [top2Excl_le_top2 x j hxpos]
        · linarith [top2_nonneg_pos x hxpos]
      · rw [if_neg hWk, if_neg fun h => hWk h.1]; simp
    linarith

end EndogLemma2Aux

open EndogBudgetAds.Equilibrium EndogLemma2Aux in
theorem solution (M : Market) (hM : M.Standing) (j k : Fin M.m) (hkj : k ≠ j)
    (σj : Strategy M.n) (V : Valuations M) (hVpos : ∀ l i, 0 < V l i)
    (hW : NoTies (W M V)) (hb : NoTies (bidsOf (deviate (sigmaStar M) j σj) V)) :
    (∑ i, if EndogBudgetAds.Equilibrium.IsTop
        (fun l => bidsOf (deviate (sigmaStar M) j σj) V l i) k then
        pay (bidsOf (deviate (sigmaStar M) j σj) V) i k else 0) ≤
      PsiBar M k V + Xi M j k σj V := by
  have hbw : ∀ i l, l ≠ j → bidsOf (deviate (sigmaStar M) j σj) V l i = W M V l i := by
    intro i l hl
    simp only [bidsOf, deviate, Function.update_of_ne hl]
    rfl
  have hpos : ∀ i l, 0 < W M V l i := fun i l => by
    unfold W
    have := hM.r_nonneg l
    have := hVpos l i
    positivity
  unfold PsiBar Xi
  refine le_trans (Finset.sum_le_sum fun i _ =>
    per_item (W M V) (bidsOf (deviate (sigmaStar M) j σj) V) i j k hkj
      (fun l hl => hbw i l hl) (fun l => hpos i l)
      (fun a c hac => hW i a c hac) (fun a c hac => hb i a c hac)) (le_of_eq ?_)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring
