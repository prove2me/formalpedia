-- Prove2me | solution 1 for FedergruenZhengRQ.OPT.optimal_cost_formula
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T07:30:06.686948+00:00
-- url     : https://prove2.me/submissions/2802aeb5-ac66-49cc-9e5c-8d4014e834c5

import Mathlib
import Definitions.Def_FedergruenZhengRQ_OPT_Model

set_option autoImplicit false

open FedergruenZhengRQ.OPT in
theorem fz503_qc (G : ℤ → ℝ) (hG : NegUnimodal G) {u v w : ℤ} (h1 : u ≤ v) (h2 : v ≤ w) :
    G v ≤ max (G u) (G w) := by
  obtain ⟨m, hA, hM⟩ := hG
  by_cases hv : v ≤ m
  · exact le_max_of_le_left (hA (Set.mem_Iic.2 (h1.trans hv)) (Set.mem_Iic.2 hv) h1)
  · push Not at hv
    exact le_max_of_le_right (hM (Set.mem_Ici.2 hv.le) (Set.mem_Ici.2 (hv.le.trans h2)) h2)

open FedergruenZhengRQ.OPT in
theorem fz503_between (G : ℤ → ℝ) (hG : NegUnimodal G) (y₁ : ℤ) (hy : ∀ t, G y₁ ≤ G t)
    {v z : ℤ} (h : (y₁ ≤ v ∧ v ≤ z) ∨ (z ≤ v ∧ v ≤ y₁)) : G v ≤ G z := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact (fz503_qc G hG h1 h2).trans (max_le (hy z) le_rfl)
  · exact (fz503_qc G hG h1 h2).trans (max_le le_rfl (hy z))

open FedergruenZhengRQ.OPT in
theorem fz503_inv (G : ℤ → ℝ) (hG : NegUnimodal G) (y₁ : ℤ) (hy : ∀ t, G y₁ ≤ G t) :
    ∀ n : ℕ, (window G y₁ n).2 - (window G y₁ n).1 = n ∧ (window G y₁ n).1 ≤ y₁ ∧
      y₁ ≤ (window G y₁ n).2 ∧
      (∑ i ∈ Finset.Icc 1 (n + 1), G (y G y₁ i) =
        ∑ x ∈ Finset.Icc (window G y₁ n).1 (window G y₁ n).2, G x) ∧
      ∀ x z : ℤ, (window G y₁ n).1 ≤ x → x ≤ (window G y₁ n).2 →
        (z < (window G y₁ n).1 ∨ (window G y₁ n).2 < z) → G x ≤ G z := by
  intro n
  induction n with
  | zero =>
    refine ⟨by simp [window], by simp [window], by simp [window], by simp [window, y], ?_⟩
    intro x z h1 h2 _
    simp only [window] at h1 h2
    have : x = y₁ := le_antisymm h2 h1
    subst this
    exact hy z
  | succ n ih =>
    obtain ⟨hd, ha, hb, hs, hm⟩ := ih
    set a := (window G y₁ n).1 with ha_def
    set b := (window G y₁ n).2 with hb_def
    have hw : window G y₁ (n + 1) = if G (a - 1) ≤ G (b + 1) then (a - 1, b) else (a, b + 1) := rfl
    have hyn : y G y₁ (n + 1 + 1) = if G (a - 1) ≤ G (b + 1) then a - 1 else b + 1 := by
      simp [y, L, R, ha_def, hb_def]
    have hsum : ∑ i ∈ Finset.Icc 1 (n + 1 + 1), G (y G y₁ i)
        = ∑ i ∈ Finset.Icc 1 (n + 1), G (y G y₁ i) + G (y G y₁ (n + 1 + 1)) :=
      Finset.sum_Icc_succ_top (by omega) _
    rw [hw, hsum, hyn, hs]
    by_cases hc : G (a - 1) ≤ G (b + 1)
    · simp only [if_pos hc]
      have hI : Finset.Icc (a - 1) b = insert (a - 1) (Finset.Icc a b) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      refine ⟨by push_cast; omega, by omega, hb, ?_, ?_⟩
      · rw [hI, Finset.sum_insert (by simp), add_comm]
      · intro x z h1 h2 h3
        by_cases hx : a ≤ x
        · exact hm x z hx h2 (by omega)
        · have hx' : x = a - 1 := by omega
          subst hx'
          rcases h3 with h3 | h3
          · exact fz503_between G hG y₁ hy (Or.inr ⟨h3.le, by omega⟩)
          · exact hc.trans (fz503_between G hG y₁ hy (Or.inl ⟨by omega, by omega⟩))
    · simp only [if_neg hc]
      push Not at hc
      have hI : Finset.Icc a (b + 1) = insert (b + 1) (Finset.Icc a b) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      refine ⟨by push_cast; omega, ha, by omega, ?_, ?_⟩
      · rw [hI, Finset.sum_insert (by simp), add_comm]
      · intro x z h1 h2 h3
        by_cases hx : x ≤ b
        · exact hm x z h1 hx (by omega)
        · have hx' : x = b + 1 := by omega
          subst hx'
          rcases h3 with h3 | h3
          · exact hc.le.trans (fz503_between G hG y₁ hy (Or.inr ⟨by omega, by omega⟩))
          · exact fz503_between G hG y₁ hy (Or.inl ⟨by omega, h3.le⟩)

theorem fz503_exchange (G : ℤ → ℝ) (W S : Finset ℤ) (hcard : S.card = W.card)
    (hW : W.Nonempty) (hsep : ∀ x ∈ W, ∀ z, z ∉ W → G x ≤ G z) :
    ∑ x ∈ W, G x ≤ ∑ x ∈ S, G x := by
  obtain ⟨x0, hx0, hmax⟩ := W.exists_max_image G hW
  have h1 := Finset.sum_inter_add_sum_sdiff S W G
  have h2 := Finset.sum_inter_add_sum_sdiff W S G
  rw [Finset.inter_comm] at h2
  have c1 := Finset.card_sdiff_add_card_inter S W
  have c2 := Finset.card_sdiff_add_card_inter W S
  rw [Finset.inter_comm] at c2
  have hc : (W \ S).card = (S \ W).card := by omega
  have k1 : ∑ x ∈ W \ S, G x ≤ (W \ S).card • G x0 :=
    Finset.sum_le_card_nsmul _ _ _ (fun x hx => hmax x (Finset.mem_sdiff.1 hx).1)
  have k2 : (S \ W).card • G x0 ≤ ∑ x ∈ S \ W, G x :=
    Finset.card_nsmul_le_sum _ _ _ (fun z hz => hsep x0 hx0 z (Finset.mem_sdiff.1 hz).2)
  rw [hc] at k1
  linarith

open FedergruenZhengRQ.OPT in
theorem solution (κ : ℝ) (hκ : 0 < κ) (G : ℤ → ℝ) (hG : NegUnimodal G)
    (y₁ : ℤ) (hy₁ : ∀ t, G y₁ ≤ G t) (Q : ℕ) (hQ : 1 ≤ Q) :
    IsLeast (Set.range fun r : ℤ => cost κ G r Q) (Cstar κ G y₁ Q) := by
  obtain ⟨n, rfl⟩ : ∃ n, Q = n + 1 := ⟨Q - 1, by omega⟩
  obtain ⟨hd, ha, hb, hs, hm⟩ := fz503_inv G hG y₁ hy₁ n
  set a := (window G y₁ n).1 with ha_def
  set b := (window G y₁ n).2 with hb_def
  have hC : Cstar κ G y₁ (n + 1) = (κ + ∑ x ∈ Finset.Icc a b, G x) / ((n + 1 : ℕ) : ℝ) := by
    unfold Cstar; rw [hs]
  have hQpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  constructor
  · refine ⟨a - 1, ?_⟩
    simp only [cost]
    rw [hC]
    congr 2
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext x
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    push_cast
    omega
  · rintro _ ⟨r, rfl⟩
    rw [hC]
    simp only [cost]
    apply div_le_div_of_nonneg_right _ hQpos.le
    have key := fz503_exchange G (Finset.Icc a b) (Finset.Ioc r (r + ((n + 1 : ℕ) : ℤ)))
      (by simp only [Int.card_Icc, Int.card_Ioc]; push_cast; omega)
      ⟨a, by simp only [Finset.mem_Icc]; omega⟩
      (by
        intro x hx z hz
        simp only [Finset.mem_Icc] at hx hz
        exact hm x z hx.1 hx.2 (by omega))
    linarith
