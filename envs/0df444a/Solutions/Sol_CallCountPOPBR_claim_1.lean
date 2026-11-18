-- Prove2me | solution 1 for CallCountPOPBR.claim_1
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T15:33:38.424204+00:00
-- url     : https://prove2.me/submissions/b6aff0b2-134c-4316-8af0-ee553e4f0011

import Definitions.Def_CallCountPOPBR_wt

set_option autoImplicit false

namespace CL1Aux
open CallCountPOPBR

lemma wt_rec (n : ℕ) : wt n = n % 2 + wt (n / 2) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [wt]
  · unfold wt
    rw [Nat.digits_def' (by norm_num) hn, List.sum_cons]

lemma wt_add_aux : ∀ N a b c, a + b + c = N → c ≤ 1 → wt (a + b + c) ≤ wt a + wt b + c := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro a b c hN hc
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · have ha : a = 0 := by omega
      have hb : b = 0 := by omega
      have hc0 : c = 0 := by omega
      subst ha hb hc0; simp
    · set t := a % 2 + b % 2 + c with ht
      have h1 : (a + b + c) / 2 = a / 2 + b / 2 + t / 2 := by omega
      have h2 : (a + b + c) % 2 = t % 2 := by omega
      have hlt : a / 2 + b / 2 + t / 2 < N := by omega
      have := ih _ hlt (a / 2) (b / 2) (t / 2) rfl (by omega)
      rw [wt_rec (a + b + c), wt_rec a, wt_rec b, h1, h2]
      have ht3 : t ≤ 3 := by omega
      have : t % 2 + t / 2 ≤ t := by omega
      omega

lemma wt_add (a b : ℕ) : wt (a + b) ≤ wt a + wt b := by
  have := wt_add_aux (a + b + 0) a b 0 rfl (by norm_num)
  simpa using this

lemma wt_mul_two_pow (c e : ℕ) : wt (c * 2 ^ e) = wt c := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [wt_rec, pow_succ, ← mul_assoc]
    rw [Nat.mul_mod_left, Nat.mul_div_cancel _ (by norm_num), ih, zero_add]

lemma wt_le_of_lt (k : ℕ) : ∀ c, c < 2 ^ k → wt c ≤ k := by
  induction k with
  | zero => intro c hc; simp at hc; subst hc; simp [wt]
  | succ k ih =>
    intro c hc
    rw [wt_rec]
    have : c / 2 < 2 ^ k := by rw [pow_succ] at hc; omega
    have := ih _ this
    omega

lemma wt_le_of_le (k c : ℕ) (hc : c ≤ 2 ^ k) : wt c ≤ k + 1 :=
  wt_le_of_lt (k + 1) c (by rw [pow_succ]; have := Nat.one_le_two_pow (n := k); omega)

lemma wt_sum (G : Finset ℕ) (f : ℕ → ℕ) : wt (∑ e ∈ G, f e) ≤ ∑ e ∈ G, wt (f e) := by
  induction G using Finset.induction_on with
  | empty => simp [wt]
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx]
    exact (wt_add _ _).trans (by omega)

lemma ext_rep (G G' : Finset ℕ) (hG : G ⊆ G') (c : ℕ → ℕ) (B x : ℕ) (hc : ∀ e, c e ≤ B)
    (hx : x = ∑ e ∈ G, c e * 2 ^ e) :
    ∃ c' : ℕ → ℕ, (∀ e, c' e ≤ B) ∧ x = ∑ e ∈ G', c' e * 2 ^ e := by
  refine ⟨fun e => if e ∈ G then c e else 0, ?_, ?_⟩
  · intro e; dsimp only; split_ifs
    · exact hc e
    · exact Nat.zero_le _
  · rw [hx, ← Finset.sum_subset hG]
    · apply Finset.sum_congr rfl
      intro e he; simp [he]
    · intro e _ he; simp [he]

lemma pow_rep (G : Finset ℕ) (e₀ : ℕ) (he : e₀ ∈ G) :
    2 ^ e₀ = ∑ e ∈ G, (if e = e₀ then 1 else 0) * 2 ^ e := by
  simp [he]

lemma invariant (F : ℕ → ℕ) (K : ℕ)
    (hF : ∀ k, 1 ≤ k → k ≤ K → ∃ x y, F k = x + y ∧
      ((∃ e, x = 2 ^ e) ∨ ∃ i, 1 ≤ i ∧ i < k ∧ x = F i) ∧
      ((∃ e, y = 2 ^ e) ∨ ∃ i, 1 ≤ i ∧ i < k ∧ y = F i)) :
    ∀ k, k ≤ K → ∃ G : Finset ℕ, G.card ≤ 2 * k ∧ ∀ i, 1 ≤ i → i ≤ k →
      ∃ c : ℕ → ℕ, (∀ e, c e ≤ 2 ^ i) ∧ F i = ∑ e ∈ G, c e * 2 ^ e := by
  intro k
  induction k with
  | zero => intro _; exact ⟨∅, by simp, fun i h1 h2 => by omega⟩
  | succ k ih =>
    intro hk
    obtain ⟨G, hGc, hG⟩ := ih (by omega)
    obtain ⟨x, y, hxy, hx, hy⟩ := hF (k + 1) (by omega) hk
    -- representation of a summand over insert e G
    have hsum : ∀ z, ((∃ e, z = 2 ^ e) ∨ ∃ i, 1 ≤ i ∧ i < k + 1 ∧ z = F i) →
        ∃ ez, ∀ G' : Finset ℕ, insert ez G ⊆ G' →
          ∃ c : ℕ → ℕ, (∀ e, c e ≤ 2 ^ k) ∧ z = ∑ e ∈ G', c e * 2 ^ e := by
      intro z hz
      rcases hz with ⟨e, rfl⟩ | ⟨i, hi1, hik, rfl⟩
      · refine ⟨e, fun G' hG' => ⟨fun e' => if e' = e then 1 else 0, ?_, ?_⟩⟩
        · intro e'; dsimp only; split_ifs
          · exact Nat.one_le_two_pow
          · exact Nat.zero_le _
        · exact pow_rep G' e (hG' (Finset.mem_insert_self _ _))
      · refine ⟨0, fun G' hG' => ?_⟩
        obtain ⟨c, hc, hci⟩ := hG i hi1 (by omega)
        have hc' : ∀ e, c e ≤ 2 ^ k := fun e =>
          (hc e).trans (Nat.pow_le_pow_right (by norm_num) (by omega))
        exact ext_rep G G' ((Finset.subset_insert _ _).trans hG') c _ _ hc' hci
    obtain ⟨ex, hex⟩ := hsum x hx
    obtain ⟨ey, hey⟩ := hsum y hy
    refine ⟨insert ex (insert ey G), ?_, ?_⟩
    · have := Finset.card_insert_le ex (insert ey G)
      have := Finset.card_insert_le ey G
      omega
    · intro i hi1 hik
      rcases Nat.lt_or_ge i (k + 1) with hlt | hge
      · obtain ⟨c, hc, hci⟩ := hG i hi1 (by omega)
        exact ext_rep G _ ((Finset.subset_insert _ _).trans (Finset.subset_insert _ _)) c _ _ hc hci
      · have hi : i = k + 1 := by omega
        subst hi
        obtain ⟨cx, hcx, hx'⟩ := hex (insert ex (insert ey G)) (by
          intro e he
          rcases Finset.mem_insert.1 he with rfl | he
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem he))
        obtain ⟨cy, hcy, hy'⟩ := hey (insert ex (insert ey G)) (by
          intro e he
          rcases Finset.mem_insert.1 he with rfl | he
          · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
          · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem he))
        refine ⟨fun e => cx e + cy e, ?_, ?_⟩
        · intro e; have := hcx e; have := hcy e; rw [pow_succ]; dsimp only; omega
        · rw [hxy, hx', hy', ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro e _; ring

end CL1Aux

open CallCountPOPBR in
theorem solution (F : ℕ → ℕ) (K : ℕ)
    (hF : ∀ k, 1 ≤ k → k ≤ K → ∃ x y, F k = x + y ∧
      ((∃ e, x = 2 ^ e) ∨ ∃ i, 1 ≤ i ∧ i < k ∧ x = F i) ∧
      ((∃ e, y = 2 ^ e) ∨ ∃ i, 1 ≤ i ∧ i < k ∧ y = F i)) :
    ∀ k, 1 ≤ k → k ≤ K →
      wt (F k) ≤ 2 * k * (k + 1) ∧ ∀ n, K + 1 ≤ n → 2 * k * (k + 1) ≤ 2 * n ^ 2 := by
  intro k hk1 hkK
  refine ⟨?_, ?_⟩
  · obtain ⟨G, hGc, hG⟩ := CL1Aux.invariant F K hF k hkK
    obtain ⟨c, hc, hFk⟩ := hG k hk1 le_rfl
    rw [hFk]
    calc wt (∑ e ∈ G, c e * 2 ^ e) ≤ ∑ e ∈ G, wt (c e * 2 ^ e) := CL1Aux.wt_sum G _
      _ = ∑ e ∈ G, wt (c e) := by
          apply Finset.sum_congr rfl; intro e _; exact CL1Aux.wt_mul_two_pow _ _
      _ ≤ ∑ e ∈ G, (k + 1) := Finset.sum_le_sum (fun e _ => CL1Aux.wt_le_of_le k _ (hc e))
      _ = G.card * (k + 1) := by simp
      _ ≤ 2 * k * (k + 1) := Nat.mul_le_mul_right _ hGc
  · intro n hn
    have h1 : k + 1 ≤ n := by omega
    have h2 : k ≤ n := by omega
    have := Nat.mul_le_mul h2 h1
    nlinarith
