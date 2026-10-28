-- Prove2me | solution 1 for BalancedGames.Comb.theorem_12
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-25T07:18:05.192969+00:00
-- url     : https://prove2.me/submissions/86d5938e-4d9d-422e-855e-c674c50b07fe

import Mathlib
import Definitions.Def_BalancedGames_Comb_Basic

set_option autoImplicit false

namespace BGDisproof9c

open BalancedGames.Comb

/-! Counterexample to Definition-1 condition 2 for `BG+(11)`.
Ground set: six coalitions `Sk k` of the 11 players.  Player `i` lies in `Sk k` iff `k`
belongs to block `i` of the list
`012, 013, 024, 035, 045, 125, 134, 145, 234, 235, 345` (blocks 0..9 cover every `k`
exactly five times and contain no complementary pair; block 10 = 345 is the complement of
block 0 = 012). -/

def Sk : Fin 6 → Finset (Fin 11) :=
  ![{0, 1, 2, 3, 4}, {0, 1, 5, 6, 7}, {0, 2, 5, 8, 9}, {1, 3, 6, 8, 9, 10},
    {2, 4, 6, 7, 8, 10}, {3, 4, 5, 7, 9, 10}]

theorem Sk_ne_univ : ∀ k, Sk k ≠ Finset.univ := by decide

theorem Sk_inj : ∀ k k', Sk k = Sk k' → k = k' := by decide

theorem empty_ne_univ : (∅ : Finset (Fin 11)) ≠ Finset.univ := by decide

theorem empty_ne_Sk : ∀ k, (∅ : Finset (Fin 11)) ≠ Sk k := by decide

theorem cover_key : ∀ i j : Fin 11, (∀ k : Fin 6, i ∈ Sk k ∨ j ∈ Sk k) →
    (i = 0 ∧ j = 10) ∨ (i = 10 ∧ j = 0) := by decide

theorem compl_0_10 : ∀ k : Fin 6, ((0 : Fin 11) ∈ Sk k ↔ (10 : Fin 11) ∉ Sk k) := by decide

theorem compl_10_0 : ∀ k : Fin 6, ((10 : Fin 11) ∈ Sk k ↔ (0 : Fin 11) ∉ Sk k) := by decide

/-- The game with value `1` on `N`, `w k` on `Sk k`, and `0` elsewhere. -/
noncomputable def fg (w : Fin 6 → ℝ) : Game 11 :=
  fun S => (if S = Finset.univ then 1 else 0) + ∑ k, if S = Sk k then w k else 0

theorem fg_univ (w : Fin 6 → ℝ) : fg w Finset.univ = 1 := by
  unfold fg
  rw [if_pos rfl]
  have : ∀ k, (if (Finset.univ : Finset (Fin 11)) = Sk k then w k else 0) = 0 := fun k =>
    if_neg (fun h => Sk_ne_univ k h.symm)
  simp only [this, Finset.sum_const_zero, add_zero]

theorem fg_Sk (w : Fin 6 → ℝ) (k : Fin 6) : fg w (Sk k) = w k := by
  unfold fg
  rw [if_neg (Sk_ne_univ k), zero_add]
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hb
    rw [if_neg]
    intro h
    exact hb (Sk_inj _ _ h.symm)
  · intro h; exact absurd (Finset.mem_univ k) h

theorem fg_other (w : Fin 6 → ℝ) (S : Finset (Fin 11)) (hU : S ≠ Finset.univ)
    (hk : ∀ k, S ≠ Sk k) : fg w S = 0 := by
  unfold fg
  rw [if_neg hU, zero_add]
  exact Finset.sum_eq_zero (fun k _ => if_neg (hk k))

theorem game_ext (g h : Game 11) (hU : g Finset.univ = h Finset.univ)
    (hk : ∀ k, g (Sk k) = h (Sk k))
    (ho : ∀ S, S ≠ Finset.univ → (∀ k, S ≠ Sk k) → g S = h S) : g = h := by
  funext S
  by_cases h1 : S = Finset.univ
  · subst h1; exact hU
  by_cases h2 : ∃ k, S = Sk k
  · obtain ⟨k, rfl⟩ := h2; exact hk k
  · push_neg at h2
    exact ho S h1 h2

/-- Membership criterion for `BG+(11)` of a game `fg w`, from an explicit core point. -/
theorem fg_mem (w : Fin 6 → ℝ) (hw0 : ∀ k, 0 ≤ w k) (x : Fin 11 → ℝ)
    (hx0 : ∀ i, 0 ≤ x i) (hxs : ∑ i, x i = 1)
    (hxk : ∀ k, w k ≤ ∑ i ∈ Sk k, x i) : fg w ∈ BGplus 11 := by
  refine ⟨⟨?_, ?_, fg_univ w⟩, x, ?_, ?_⟩
  · exact fg_other w ∅ empty_ne_univ empty_ne_Sk
  · intro S
    unfold fg
    refine add_nonneg (by split_ifs <;> norm_num) (Finset.sum_nonneg fun k _ => ?_)
    split_ifs
    · exact hw0 k
    · exact le_refl 0
  · rw [fg_univ]; exact hxs
  · intro S _
    by_cases h1 : S = Finset.univ
    · subst h1; rw [fg_univ, hxs]
    by_cases h2 : ∃ k, S = Sk k
    · obtain ⟨k, rfl⟩ := h2; rw [fg_Sk]; exact hxk k
    · push_neg at h2
      rw [fg_other w S h1 h2]
      exact Finset.sum_nonneg fun i _ => hx0 i

noncomputable def wstar (a : Fin 11) : Fin 6 → ℝ := fun k => if a ∈ Sk k then 1 else 0

theorem wstar_mem (a : Fin 11) : fg (wstar a) ∈ BGplus 11 := by
  refine fg_mem (wstar a) (fun k => by unfold wstar; split_ifs <;> norm_num)
    (fun i => if i = a then 1 else 0) (fun i => by split_ifs <;> norm_num) ?_ ?_
  · simp
  · intro k
    rw [Finset.sum_ite_eq']
    unfold wstar
    split_ifs <;> norm_num

noncomputable def wq : Fin 6 → ℝ := fun k => if (1 : Fin 11) ∈ Sk k then 4 / 9 else 5 / 9

noncomputable def xq : Fin 11 → ℝ := fun i => if i = 1 ∨ i = 10 then 0 else 1 / 9

theorem q_mem : fg wq ∈ BGplus 11 := by
  refine fg_mem wq (fun k => by unfold wq; split_ifs <;> norm_num) xq
    (fun i => by unfold xq; split_ifs <;> norm_num) ?_ ?_
  · simp [xq, Fin.sum_univ_succ]
    norm_num
  · intro k
    fin_cases k <;> simp [wq, xq, Sk, Finset.sum_insert] <;> norm_num

/-! General facts about `BG+(n)`. -/

theorem BG_bounds {n : ℕ} (w : Game n) (hw : w ∈ BGplus n) (S : Finset (Fin n)) :
    0 ≤ w S ∧ w S ≤ 1 := by
  obtain ⟨⟨_, hnn, h1⟩, y, hys, hyS⟩ := hw
  refine ⟨hnn S, ?_⟩
  have hy0 : ∀ i, 0 ≤ y i := by
    intro i
    have := hyS {i} (Finset.subset_univ _)
    simp only [Finset.sum_singleton] at this
    exact le_trans (hnn _) this
  calc w S ≤ ∑ i ∈ S, y i := hyS S (Finset.subset_univ _)
    _ ≤ ∑ i ∈ Finset.univ, y i :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hy0 i)
    _ = 1 := by rw [hys, h1]

theorem zeroOne_extreme {n : ℕ} (v : Game n) (hv : v ∈ BGplus n)
    (hz : ∀ S, v S = 0 ∨ v S = 1) : v ∈ Set.extremePoints ℝ (BGplus n) := by
  rw [mem_extremePoints]
  refine ⟨hv, fun x₁ h₁ x₂ h₂ hseg => ?_⟩
  obtain ⟨a, b, ha, hb, hab, he⟩ := hseg
  have key : ∀ S, x₁ S = v S ∧ x₂ S = v S := by
    intro S
    have hS : a * x₁ S + b * x₂ S = v S := by
      have := congrFun he S
      simpa using this
    obtain ⟨l1, u1⟩ := BG_bounds x₁ h₁ S
    obtain ⟨l2, u2⟩ := BG_bounds x₂ h₂ S
    rcases hz S with h | h
    · rw [h] at hS ⊢
      have e1 : a * x₁ S = 0 := by nlinarith [mul_nonneg ha.le l1, mul_nonneg hb.le l2]
      have e2 : b * x₂ S = 0 := by nlinarith [mul_nonneg ha.le l1, mul_nonneg hb.le l2]
      exact ⟨(mul_eq_zero.mp e1).resolve_left ha.ne', (mul_eq_zero.mp e2).resolve_left hb.ne'⟩
    · rw [h] at hS ⊢
      have e1 : a * (1 - x₁ S) = 0 := by
        nlinarith [mul_nonneg ha.le (sub_nonneg.mpr u1), mul_nonneg hb.le (sub_nonneg.mpr u2)]
      have e2 : b * (1 - x₂ S) = 0 := by
        nlinarith [mul_nonneg ha.le (sub_nonneg.mpr u1), mul_nonneg hb.le (sub_nonneg.mpr u2)]
      have f1 := (mul_eq_zero.mp e1).resolve_left ha.ne'
      have f2 := (mul_eq_zero.mp e2).resolve_left hb.ne'
      constructor <;> linarith
  exact ⟨funext fun S => (key S).1, funext fun S => (key S).2⟩

theorem veto {n : ℕ} (v : Game n) (hv : v ∈ BGplus n) :
    ∃ i, ∀ S, v S = 1 → i ∈ S := by
  obtain ⟨⟨_, hnn, h1⟩, y, hys, hyS⟩ := hv
  have hy0 : ∀ i, 0 ≤ y i := by
    intro i
    have := hyS {i} (Finset.subset_univ _)
    simp only [Finset.sum_singleton] at this
    exact le_trans (hnn _) this
  rw [h1] at hys
  obtain ⟨i, hi⟩ : ∃ i, 0 < y i := by
    by_contra hc
    push_neg at hc
    have : ∑ i ∈ Finset.univ, y i ≤ 0 := Finset.sum_nonpos (fun i _ => hc i)
    linarith
  refine ⟨i, fun S hS => ?_⟩
  by_contra hiS
  have h2 := hyS S (Finset.subset_univ _)
  rw [hS] at h2
  have h3 : ∑ j ∈ S, y j ≤ ∑ j ∈ Finset.univ.erase i, y j :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (fun j hj => Finset.mem_erase.mpr ⟨fun e => hiS (e ▸ hj), Finset.mem_univ j⟩)
      (fun j _ _ => hy0 j)
  have h4 := Finset.add_sum_erase Finset.univ y (Finset.mem_univ i)
  linarith

/-! The two vertices and the failure of the swap condition. -/

theorem v_ne : fg (wstar 0) ≠ fg (wstar 10) := by
  intro h
  have := congrFun h (Sk 0)
  rw [fg_Sk, fg_Sk] at this
  simp [wstar, Sk] at this

theorem v_ne' : fg (wstar 10) ≠ fg (wstar 0) := fun h => v_ne h.symm

theorem v_zeroOne (a : Fin 11) : ∀ S, fg (wstar a) S = 0 ∨ fg (wstar a) S = 1 := by
  intro S
  by_cases h1 : S = Finset.univ
  · subst h1; right; exact fg_univ _
  by_cases h2 : ∃ k, S = Sk k
  · obtain ⟨k, rfl⟩ := h2
    rw [fg_Sk]; unfold wstar; split_ifs <;> simp
  · push_neg at h2
    left; exact fg_other _ S h1 h2

theorem v_ext (a : Fin 11) : fg (wstar a) ∈ Set.extremePoints ℝ (BGplus 11) :=
  zeroOne_extreme _ (wstar_mem a) (v_zeroOne a)

theorem midpoint_eq :
    (1 / 2 : ℝ) • fg (wstar 0) + (1 / 2 : ℝ) • fg (wstar 10) =
      (1 / 10 : ℝ) • fg (wstar 1) + (9 / 10 : ℝ) • fg wq := by
  apply game_ext
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, fg_univ]; norm_num
  · intro k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, fg_Sk]
    fin_cases k <;> simp [wstar, wq, Sk] <;> norm_num
  · intro S h1 h2
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, fg_other _ S h1 h2]
    norm_num

theorem not_adj : ¬ Hirsch.Adj (BGplus 11) (fg (wstar 0)) (fg (wstar 10)) := by
  rintro ⟨_, hE⟩
  have hm : (1 / 2 : ℝ) • fg (wstar 0) + (1 / 2 : ℝ) • fg (wstar 10) ∈
      segment ℝ (fg (wstar 0)) (fg (wstar 10)) :=
    ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩
  have ho : (1 / 2 : ℝ) • fg (wstar 0) + (1 / 2 : ℝ) • fg (wstar 10) ∈
      openSegment ℝ (fg (wstar 1)) (fg wq) :=
    ⟨1 / 10, 9 / 10, by norm_num, by norm_num, by norm_num, midpoint_eq.symm⟩
  have hp := hE.left_mem_of_mem_openSegment (wstar_mem 1) q_mem hm ho
  obtain ⟨a, b, _, _, _, he⟩ := hp
  have e0 := congrFun he (Sk 0)
  have e2 := congrFun he (Sk 2)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, fg_Sk] at e0 e2
  simp [wstar, Sk] at e0 e2
  linarith

theorem pin (v₃ v₄ : Game 11) (h₃ : v₃ ∈ BGplus 11) (h₄ : v₄ ∈ BGplus 11)
    (z₃ : ∀ S, v₃ S = 0 ∨ v₃ S = 1) (z₄ : ∀ S, v₄ S = 0 ∨ v₄ S = 1)
    (hs : fg (wstar 0) + fg (wstar 10) = v₃ + v₄) (a b : Fin 11)
    (ha : ∀ S, v₃ S = 1 → a ∈ S) (hb : ∀ S, v₄ S = 1 → b ∈ S)
    (hab : ∀ k, a ∈ Sk k ↔ b ∉ Sk k) : v₃ = fg (wstar a) := by
  apply game_ext
  · rw [fg_univ]; exact h₃.1.2.2
  · intro k
    have e := congrFun hs (Sk k)
    simp only [Pi.add_apply, fg_Sk] at e
    have hsum : wstar 0 k + wstar 10 k = 1 := by
      unfold wstar
      have := compl_0_10 k
      by_cases h0 : (0 : Fin 11) ∈ Sk k
      · rw [if_pos h0, if_neg (this.mp h0)]; norm_num
      · have h10 : (10 : Fin 11) ∈ Sk k := by
          by_contra h; exact h0 (this.mpr h)
        rw [if_neg h0, if_pos h10]; norm_num
    rw [fg_Sk]
    unfold wstar
    rcases z₃ (Sk k) with h | h
    · have h4 : v₄ (Sk k) = 1 := by linarith
      have hbk := hb _ h4
      rw [if_neg (fun hak => (hab k).mp hak hbk), h]
    · rw [if_pos (ha _ h), h]
  · intro S h1 h2
    have e := congrFun hs S
    simp only [Pi.add_apply, fg_other _ S h1 h2] at e
    rw [fg_other _ S h1 h2]
    have := (BG_bounds v₃ h₃ S).1
    have := (BG_bounds v₄ h₄ S).1
    linarith

theorem not_comb : ¬ IsCombinatorial (BGplus 11) := by
  intro hc
  obtain ⟨v₃, hv₃, v₄, hv₄, _, h31, h32, _, _, hs⟩ :=
    hc.2 _ (v_ext 0) _ (v_ext 10) v_ne not_adj
  have m₃ : v₃ ∈ BGplus 11 := hv₃.1
  have m₄ : v₄ ∈ BGplus 11 := hv₄.1
  have z₃ := hc.1 v₃ hv₃
  have z₄ := hc.1 v₄ hv₄
  obtain ⟨i, hi⟩ := veto v₃ m₃
  obtain ⟨j, hj⟩ := veto v₄ m₄
  have hcov : ∀ k : Fin 6, i ∈ Sk k ∨ j ∈ Sk k := by
    intro k
    have e := congrFun hs (Sk k)
    simp only [Pi.add_apply, fg_Sk] at e
    have hsum : wstar 0 k + wstar 10 k = 1 := by
      unfold wstar
      have := compl_0_10 k
      by_cases h0 : (0 : Fin 11) ∈ Sk k
      · rw [if_pos h0, if_neg (this.mp h0)]; norm_num
      · have h10 : (10 : Fin 11) ∈ Sk k := by
          by_contra h; exact h0 (this.mpr h)
        rw [if_neg h0, if_pos h10]; norm_num
    rcases z₃ (Sk k) with h | h
    · right; exact hj _ (by linarith)
    · left; exact hi _ h
  rcases cover_key i j hcov with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h31 (pin v₃ v₄ m₃ m₄ z₃ z₄ hs 0 10 hi hj compl_0_10)
  · exact h32 (pin v₃ v₄ m₃ m₄ z₃ z₄ hs 10 0 hi hj compl_10_0)

end BGDisproof9c

open BalancedGames.Comb in
theorem solution : ¬ (∀ (n : ℕ),
    (IsPolytope (BGplus n) ∧ IsCombinatorial (BGplus n)) ∧
      IsHamiltonConnected (adjGraph (BGplus n))) := by
  intro H
  exact BGDisproof9c.not_comb (H 11).1.2
