-- Prove2me | solution 1 for FedergruenZhengRQ.OPT.corollary1_reorder_monotone
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T11:53:41.852162+00:00
-- url     : https://prove2.me/submissions/07086857-9c94-44af-9263-2ea7a67089ba

import Mathlib
import Definitions.Def_FedergruenZhengRQ_OPT_Model



namespace FedergruenZhengRQ.OPT

lemma fz_left (G : ℤ → ℝ) (hG : NegUnimodal G) (y₁ : ℤ) (hy₁ : ∀ t, G y₁ ≤ G t)
    (t s : ℤ) (hts : t ≤ s) (hs : s ≤ y₁) : G s ≤ G t := by
  obtain ⟨m, hA, hM⟩ := hG
  by_cases hsm : s ≤ m
  · exact hA (Set.mem_Iic.2 (le_trans hts hsm)) (Set.mem_Iic.2 hsm) hts
  · rw [not_le] at hsm
    have : G s ≤ G y₁ := hM (Set.mem_Ici.2 hsm.le) (Set.mem_Ici.2 (by omega)) hs
    linarith [hy₁ t]

lemma fz_right (G : ℤ → ℝ) (hG : NegUnimodal G) (y₁ : ℤ) (hy₁ : ∀ t, G y₁ ≤ G t)
    (t s : ℤ) (hts : s ≤ t) (hs : y₁ ≤ s) : G s ≤ G t := by
  obtain ⟨m, hA, hM⟩ := hG
  by_cases hsm : m ≤ s
  · exact hM (Set.mem_Ici.2 hsm) (Set.mem_Ici.2 (le_trans hsm hts)) hts
  · rw [not_le] at hsm
    have : G s ≤ G y₁ := hA (Set.mem_Iic.2 (by omega)) (Set.mem_Iic.2 hsm.le) hs
    linarith [hy₁ t]

/-- invariant of the window -/
lemma fz_inv (G : ℤ → ℝ) (hG : NegUnimodal G) (y₁ : ℤ) (hy₁ : ∀ t, G y₁ ≤ G t) (n : ℕ) :
    (window G y₁ n).1 ≤ y₁ ∧ y₁ ≤ (window G y₁ n).2 ∧
    (window G y₁ n).2 - (window G y₁ n).1 = n ∧
    ∀ x, (window G y₁ n).1 ≤ x → x ≤ (window G y₁ n).2 →
      G x ≤ G ((window G y₁ n).1 - 1) ∧ G x ≤ G ((window G y₁ n).2 + 1) := by
  induction n with
  | zero =>
    simp only [window]
    refine ⟨le_rfl, le_rfl, by simp, fun x h1 h2 => ?_⟩
    have : x = y₁ := le_antisymm h2 h1
    subst this; exact ⟨hy₁ _, hy₁ _⟩
  | succ n ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    set a := (window G y₁ n).1 with ha
    set b := (window G y₁ n).2 with hb
    have hw : window G y₁ (n+1) = if G (a - 1) ≤ G (b + 1) then (a - 1, b) else (a, b + 1) := by
      simp only [window, ha, hb]
    rw [hw]
    split_ifs with hc
    · simp only
      refine ⟨by omega, h2, by push_cast; omega, fun x hx1 hx2 => ?_⟩
      have hl : G (a - 1) ≤ G (a - 1 - 1) := fz_left G hG y₁ hy₁ _ _ (by omega) (by omega)
      by_cases hxa : x = a - 1
      · subst hxa; exact ⟨hl, hc⟩
      · have := h4 x (by omega) hx2
        exact ⟨le_trans this.1 hl, this.2⟩
    · simp only
      rw [not_le] at hc
      refine ⟨h1, by omega, by push_cast; omega, fun x hx1 hx2 => ?_⟩
      have hr : G (b + 1) ≤ G (b + 1 + 1) := fz_right G hG y₁ hy₁ _ _ (by omega) (by omega)
      by_cases hxb : x = b + 1
      · subst hxb; exact ⟨hc.le, hr⟩
      · have := h4 x hx1 (by omega)
        exact ⟨this.1, le_trans this.2 hr⟩

lemma fz_window_succ (G : ℤ → ℝ) (y₁ : ℤ) (n : ℕ) :
    window G y₁ (n+1) = if G ((window G y₁ n).1 - 1) ≤ G ((window G y₁ n).2 + 1) then
      ((window G y₁ n).1 - 1, (window G y₁ n).2) else ((window G y₁ n).1, (window G y₁ n).2 + 1) := by
  rfl

lemma fz_y_succ (G : ℤ → ℝ) (y₁ : ℤ) (n : ℕ) :
    y G y₁ (n+2) = if G ((window G y₁ n).1 - 1) ≤ G ((window G y₁ n).2 + 1) then
      (window G y₁ n).1 - 1 else (window G y₁ n).2 + 1 := by
  simp [y, L, R]

/-- the image/sum of the first n+1 points -/
lemma fz_image (G : ℤ → ℝ) (y₁ : ℤ) (n : ℕ) :
    (Finset.Icc 1 (n+1)).image (y G y₁) = Finset.Icc (window G y₁ n).1 (window G y₁ n).2 ∧
    ∑ i ∈ Finset.Icc 1 (n+1), G (y G y₁ i) = ∑ t ∈ Finset.Icc (window G y₁ n).1 (window G y₁ n).2, G t := by
  induction n with
  | zero => simp [window, y]
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    have hI : Finset.Icc 1 (n+1+1) = insert (n+2) (Finset.Icc 1 (n+1)) := by
      ext i; simp; omega
    have hn : (n+2) ∉ Finset.Icc 1 (n+1) := by simp
    rw [hI, Finset.image_insert, Finset.sum_insert hn, h1, h2, fz_y_succ, fz_window_succ]
    have hle : (window G y₁ n).1 ≤ (window G y₁ n).2 + 1 := by
      have := Finset.mem_image_of_mem (y G y₁) (show 1 ∈ Finset.Icc 1 (n+1) by simp)
      rw [h1] at this; simp at this; omega
    split_ifs with hc
    · have e : Finset.Icc ((window G y₁ n).1 - 1) (window G y₁ n).2 =
          insert ((window G y₁ n).1 - 1) (Finset.Icc (window G y₁ n).1 (window G y₁ n).2) := by
        ext t; simp; omega
      rw [e, Finset.sum_insert (by simp)]
      exact ⟨rfl, rfl⟩
    · have e : Finset.Icc (window G y₁ n).1 ((window G y₁ n).2 + 1) =
          insert ((window G y₁ n).2 + 1) (Finset.Icc (window G y₁ n).1 (window G y₁ n).2) := by
        ext t; simp; omega
      rw [e, Finset.sum_insert (by simp)]
      exact ⟨rfl, rfl⟩

lemma fz_exchange (G : ℤ → ℝ) (W T : Finset ℤ) (c : ℝ) (hcard : T.card = W.card)
    (hW : ∀ x ∈ W, G x ≤ c) (hT : ∀ t, t ∉ W → c ≤ G t) :
    ∑ x ∈ W, G x ≤ ∑ t ∈ T, G t := by
  classical
  have e1 := Finset.sum_sdiff (s₁ := W ∩ T) (s₂ := W) (f := G) Finset.inter_subset_left
  have e2 := Finset.sum_sdiff (s₁ := W ∩ T) (s₂ := T) (f := G) Finset.inter_subset_right
  have hc1 : (W \ (W ∩ T)).card = (T \ (W ∩ T)).card := by
    rw [Finset.card_sdiff_of_subset Finset.inter_subset_left,
      Finset.card_sdiff_of_subset Finset.inter_subset_right, hcard]
  have s1 : ∑ x ∈ W \ (W ∩ T), G x ≤ ∑ x ∈ W \ (W ∩ T), c :=
    Finset.sum_le_sum fun x hx => hW x (Finset.mem_sdiff.1 hx).1
  have s2 : ∑ x ∈ T \ (W ∩ T), c ≤ ∑ x ∈ T \ (W ∩ T), G x :=
    Finset.sum_le_sum fun x hx => hT x (by
      intro hxW; exact (Finset.mem_sdiff.1 hx).2 (Finset.mem_inter.2 ⟨hxW, (Finset.mem_sdiff.1 hx).1⟩))
  simp only [Finset.sum_const, nsmul_eq_mul] at s1 s2
  rw [hc1] at s1
  linarith

lemma fz_LR (G : ℤ → ℝ) (y₁ : ℤ) (n : ℕ) :
    L G y₁ (n+1) = (window G y₁ n).1 ∧ R G y₁ (n+1) = (window G y₁ n).2 := by
  simp [L, R]

theorem window_contiguous_smallest_core (G : ℤ → ℝ) (hG : NegUnimodal G) (y₁ : ℤ)
    (hy₁ : ∀ t, G y₁ ≤ G t) (Q : ℕ) (hQ : 1 ≤ Q) :
    (Finset.Icc 1 Q).image (y G y₁) = Finset.Icc (L G y₁ Q) (R G y₁ Q) ∧
    R G y₁ Q - L G y₁ Q + 1 = (Q : ℤ) ∧
    (∀ i ∈ Finset.Icc 1 Q, ∀ t : ℤ, t ∉ Finset.Icc (L G y₁ Q) (R G y₁ Q) → G (y G y₁ i) ≤ G t) ∧
    (∀ T : Finset ℤ, T.card = Q → ∑ i ∈ Finset.Icc 1 Q, G (y G y₁ i) ≤ ∑ t ∈ T, G t) := by
  obtain ⟨n, rfl⟩ : ∃ n, Q = n + 1 := ⟨Q - 1, by omega⟩
  obtain ⟨hL, hR⟩ := fz_LR G y₁ n
  rw [hL, hR]
  obtain ⟨h1, h2⟩ := fz_image G y₁ n
  obtain ⟨i1, i2, i3, i4⟩ := fz_inv G hG y₁ hy₁ n
  set a := (window G y₁ n).1
  set b := (window G y₁ n).2
  have hout : ∀ x, a ≤ x → x ≤ b → ∀ t : ℤ, t ∉ Finset.Icc a b → G x ≤ G t := by
    intro x hx1 hx2 t ht
    simp only [Finset.mem_Icc, not_and_or, not_le] at ht
    rcases ht with ht | ht
    · exact le_trans (i4 x hx1 hx2).1 (fz_left G hG y₁ hy₁ t (a-1) (by omega) (by omega))
    · exact le_trans (i4 x hx1 hx2).2 (fz_right G hG y₁ hy₁ t (b+1) (by omega) (by omega))
  refine ⟨h1, by push_cast; omega, ?_, ?_⟩
  · intro i hi t ht
    have hm := Finset.mem_image_of_mem (y G y₁) hi
    rw [h1, Finset.mem_Icc] at hm
    exact hout _ hm.1 hm.2 t ht
  · intro T hT
    rw [h2]
    apply fz_exchange G _ T (min (G (a-1)) (G (b+1)))
    · rw [hT, Int.card_Icc]; omega
    · intro x hx; rw [Finset.mem_Icc] at hx
      exact le_min (i4 x hx.1 hx.2).1 (i4 x hx.1 hx.2).2
    · intro t ht
      simp only [Finset.mem_Icc, not_and_or, not_le] at ht
      rcases ht with ht | ht
      · exact le_trans (min_le_left _ _) (fz_left G hG y₁ hy₁ t (a-1) (by omega) (by omega))
      · exact le_trans (min_le_right _ _) (fz_right G hG y₁ hy₁ t (b+1) (by omega) (by omega))

lemma fz_cost_window (κ : ℝ) (G : ℤ → ℝ) (hG : NegUnimodal G) (y₁ : ℤ)
    (hy₁ : ∀ t, G y₁ ≤ G t) (Q : ℕ) (hQ : 1 ≤ Q) :
    cost κ G (L G y₁ Q - 1) Q = Cstar κ G y₁ Q ∧
    ∀ r : ℤ, cost κ G (L G y₁ Q - 1) Q ≤ cost κ G r Q := by
  obtain ⟨h1, h2, h3, h4⟩ := window_contiguous_smallest_core G hG y₁ hy₁ Q hQ
  have hsum : ∑ t ∈ Finset.Ioc (L G y₁ Q - 1) (L G y₁ Q - 1 + Q), G t
      = ∑ i ∈ Finset.Icc 1 Q, G (y G y₁ i) := by
    have hinj : Set.InjOn (y G y₁) (Finset.Icc 1 Q) := by
      have hc := congrArg Finset.card h1
      rw [Int.card_Icc] at hc
      apply Finset.injOn_of_card_image_eq
      rw [hc]; simp; omega
    rw [← Finset.sum_image (f := G) hinj, h1]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext t; simp; omega
  have hQpos : (0:ℝ) < Q := by exact_mod_cast hQ
  have e : cost κ G (L G y₁ Q - 1) Q = Cstar κ G y₁ Q := by
    simp only [cost, Cstar]; rw [hsum]
  refine ⟨e, fun r => ?_⟩
  rw [e]
  simp only [cost, Cstar]
  apply div_le_div_of_nonneg_right _ hQpos.le
  have := h4 (Finset.Ioc r (r + Q)) (by simp)
  linarith

theorem corollary1_core (κ : ℝ) (hκ : 0 < κ) (G : ℤ → ℝ)
    (hG : NegUnimodal G) (y₁ : ℤ) (hy₁ : ∀ t, G y₁ ≤ G t)
    (Q : ℕ) (hQ : 1 ≤ Q) :
    (L G y₁ (Q + 1) = L G y₁ Q ∨ L G y₁ (Q + 1) = L G y₁ Q - 1) ∧
    (L G y₁ Q - 1) - 1 ≤ L G y₁ (Q + 1) - 1 ∧ L G y₁ (Q + 1) - 1 ≤ L G y₁ Q - 1 ∧
    (∀ r : ℤ, cost κ G (L G y₁ Q - 1) Q ≤ cost κ G r Q) ∧
    (∀ r : ℤ, cost κ G (L G y₁ (Q + 1) - 1) (Q + 1) ≤ cost κ G r (Q + 1)) := by
  have hor : L G y₁ (Q + 1) = L G y₁ Q ∨ L G y₁ (Q + 1) = L G y₁ Q - 1 := by
    obtain ⟨n, rfl⟩ : ∃ n, Q = n + 1 := ⟨Q - 1, by omega⟩
    rw [(fz_LR G y₁ (n+1)).1, (fz_LR G y₁ n).1, fz_window_succ]
    split_ifs <;> simp
  refine ⟨hor, by omega, by omega, (fz_cost_window κ G hG y₁ hy₁ Q hQ).2,
    (fz_cost_window κ G hG y₁ hy₁ (Q+1) (by omega)).2⟩

end FedergruenZhengRQ.OPT

open FedergruenZhengRQ.OPT


theorem solution (κ : ℝ) (hκ : 0 < κ) (G : ℤ → ℝ)
    (hG : NegUnimodal G) (y₁ : ℤ) (hy₁ : ∀ t, G y₁ ≤ G t)
    (Q : ℕ) (hQ : 1 ≤ Q) :
    (L G y₁ (Q + 1) = L G y₁ Q ∨ L G y₁ (Q + 1) = L G y₁ Q - 1) ∧
    (L G y₁ Q - 1) - 1 ≤ L G y₁ (Q + 1) - 1 ∧ L G y₁ (Q + 1) - 1 ≤ L G y₁ Q - 1 ∧
    (∀ r : ℤ, cost κ G (L G y₁ Q - 1) Q ≤ cost κ G r Q) ∧
    (∀ r : ℤ, cost κ G (L G y₁ (Q + 1) - 1) (Q + 1) ≤ cost κ G r (Q + 1)) := by
  exact corollary1_core κ hκ G hG y₁ hy₁ Q hQ
