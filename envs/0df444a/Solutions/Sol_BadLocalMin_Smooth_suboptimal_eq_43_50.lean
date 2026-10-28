-- Prove2me | solution 1 for BadLocalMin.Smooth.suboptimal_eq_43_50
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T20:15:30.696912+00:00
-- url     : https://prove2.me/submissions/14b93979-39bb-4fcf-adb7-04b4a5c3ba32

import Mathlib
import Definitions.Def_BadLocalMin_Smooth_Model

namespace Aux_BLM4350
open BadLocalMin.Smooth

lemma post_succ (σ : ℝ → ℝ) {d : ℕ → ℕ} {H N : ℕ} (X : Fin (d 0) → Fin N → ℝ)
    (θ : Params d H) (k : ℕ) (hk : k + 1 ≤ H) (i : Fin (d (k + 1))) (n : Fin N) :
    post σ X θ (k + 1) hk i n =
      σ ((∑ j, θ.1 ⟨k, by omega⟩ i j * post σ X θ k (by omega) j n) + θ.2 ⟨k, by omega⟩ i) := by
  rfl

lemma post_const (σ : ℝ → ℝ) {d : ℕ → ℕ} {H N : ℕ} (X : Fin (d 0) → Fin N → ℝ) (a : ℝ)
    (θ : Params d H) (h19ad : Constr19ad σ a θ) :
    ∀ k (hk1 : 1 ≤ k) (hk : k ≤ H), post σ X θ k hk = fun _ _ => σ a := by
  intro k hk1
  induction k, hk1 using Nat.le_induction with
  | base =>
    intro hk
    funext i n
    rw [post_succ]
    have h0 : ∀ j : Fin (d 0), θ.1 ⟨0, Nat.succ_pos H⟩ i j = 0 := h19ad.1 i
    simp only [h0, zero_mul, Finset.sum_const_zero, zero_add]
    rw [h19ad.2.1 (by omega) i]
  | succ k hk1 ih =>
    intro hk
    funext i n
    rw [post_succ, ih (by omega)]
    obtain ⟨_, hb⟩ := h19ad.2.2 k (by omega) hk1 i
    rw [hb, ← Finset.sum_mul]
    congr 1
    ring

noncomputable def thetaStar {d : ℕ → ℕ} {H' : ℕ} (θ' : Params d (H' + 1)) (h2 : 2 ≤ d (H' + 1))
    (t c b : ℝ) : Params d (H' + 1) :=
  (Function.update
      (Function.update θ'.1 (Fin.last (H' + 1))
        (fun (_ : Fin (d (H' + 1 + 1))) (j : Fin (d (H' + 1))) =>
          if j.val = 0 then t else if j.val = 1 then c else 0))
      ⟨H', by omega⟩
      (Function.update (θ'.1 ⟨H', by omega⟩) (⟨1, (show 1 < d (H' + 1) by omega)⟩)
        (fun _ => 0)),
    Function.update θ'.2 ⟨H', by omega⟩
      (Function.update (θ'.2 ⟨H', by omega⟩) (⟨1, (show 1 < d (H' + 1) by omega)⟩) b))

lemma star_low {d : ℕ → ℕ} {H' : ℕ} (θ' : Params d (H' + 1)) (h2 : 2 ≤ d (H' + 1))
    (t c b : ℝ) (k : ℕ) (hk : k < H') :
    (thetaStar θ' h2 t c b).1 ⟨k, by omega⟩ = θ'.1 ⟨k, by omega⟩ ∧
      (thetaStar θ' h2 t c b).2 ⟨k, by omega⟩ = θ'.2 ⟨k, by omega⟩ := by
  constructor
  · simp only [thetaStar]
    rw [Function.update_of_ne, Function.update_of_ne]
    all_goals (intro h; have := congrArg Fin.val h; simp at this; omega)
  · simp only [thetaStar]
    rw [Function.update_of_ne]
    intro h; have := congrArg Fin.val h; simp at this; omega

lemma post_low (σ : ℝ → ℝ) {d : ℕ → ℕ} {H' N : ℕ} (X : Fin (d 0) → Fin N → ℝ)
    (θ' : Params d (H' + 1)) (h2 : 2 ≤ d (H' + 1)) (t c b : ℝ) :
    ∀ k (hk : k ≤ H'), post σ X (thetaStar θ' h2 t c b) k (by omega) =
      post σ X θ' k (by omega) := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    funext i n
    rw [post_succ, post_succ, ih (by omega), (star_low θ' h2 t c b k (by omega)).1,
      (star_low θ' h2 t c b k (by omega)).2]

lemma post_top (σ : ℝ → ℝ) {d : ℕ → ℕ} {H' N : ℕ} (X : Fin (d 0) → Fin N → ℝ)
    (θ' : Params d (H' + 1)) (h2 : 2 ≤ d (H' + 1)) (t c b : ℝ) (n : Fin N) :
    post σ X (thetaStar θ' h2 t c b) (H' + 1) le_rfl ⟨0, by omega⟩ n =
        post σ X θ' (H' + 1) le_rfl ⟨0, by omega⟩ n ∧
      post σ X (thetaStar θ' h2 t c b) (H' + 1) le_rfl ⟨1, by omega⟩ n = σ b := by
  have eW : (thetaStar θ' h2 t c b).1 ⟨H', by omega⟩ =
      Function.update (θ'.1 ⟨H', by omega⟩) (⟨1, (show 1 < d (H' + 1) by omega)⟩)
        (fun _ => 0) := by
    simp only [thetaStar]; exact Function.update_self _ _ _
  have eB : (thetaStar θ' h2 t c b).2 ⟨H', by omega⟩ =
      Function.update (θ'.2 ⟨H', by omega⟩) (⟨1, (show 1 < d (H' + 1) by omega)⟩) b := by
    simp only [thetaStar]; exact Function.update_self _ _ _
  have hne : (⟨0, by omega⟩ : Fin (d (H' + 1))) ≠ ⟨1, by omega⟩ := by
    intro h; have := congrArg Fin.val h; simp at this
  constructor
  · rw [post_succ, post_succ, post_low σ X θ' h2 t c b H' le_rfl, eW, eB]
    rw [Function.update_of_ne hne, Function.update_of_ne hne]
  · rw [post_succ, eW, eB]
    simp

end Aux_BLM4350

open BadLocalMin.Smooth Aux_BLM4350 in
theorem solution (H N : ℕ) (d : ℕ → ℕ) (σ : ℝ → ℝ) (X : Fin (d 0) → Fin N → ℝ)
    (a : ℝ) (hH : 1 ≤ H) (hdH : 2 ≤ d H) (dY : Fin (d (H + 1)) → Fin N → ℝ) (hdY : dY ≠ 0)
    (θ : Params d H) (h19ad : Constr19ad σ a θ) (h19e : Constr19e θ)
    (h44 : ∃ θ' : Params d H, ∀ i : Fin (d (H + 1)),
      0 < ∑ n, dY i n * post σ X θ' H le_rfl ⟨0, by omega⟩ n) :
    0 < loss σ X (fun i n => σ a - dY i n) θ ∧
      ∃ θstar : Params d H,
        loss σ X (fun i n => σ a - dY i n) θstar < loss σ X (fun i n => σ a - dY i n) θ := by
  have hout : ∀ i n, output σ X θ i n = σ a := by
    intro i n
    unfold output
    rw [post_const σ X a θ h19ad H hH le_rfl]
    simp only [h19e i]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    simp only [Fin.val_last]
    have : (d H : ℝ) ≠ 0 := by
      have : (2 : ℝ) ≤ d H := by exact_mod_cast hdH
      linarith
    field_simp
  have hlossθ : loss σ X (fun i n => σ a - dY i n) θ = ∑ i, ∑ n, dY i n ^ 2 := by
    unfold loss
    simp only [hout]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro n _
    ring
  rw [hlossθ]
  obtain ⟨H', rfl⟩ : ∃ H', H = H' + 1 := ⟨H - 1, by omega⟩
  obtain ⟨i0, n0, hin⟩ : ∃ i n, dY i n ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hdY (funext fun i => funext fun n => hc i n)
  refine ⟨Finset.sum_pos' (fun i _ => Finset.sum_nonneg (fun n _ => sq_nonneg _))
    ⟨i0, Finset.mem_univ _, Finset.sum_pos' (fun n _ => sq_nonneg _)
      ⟨n0, Finset.mem_univ _, by positivity⟩⟩, ?_⟩
  obtain ⟨θ', h44'⟩ := h44
  obtain ⟨p, hp⟩ : ∃ p : Fin N → ℝ,
      ∀ n, post σ X θ' (H' + 1) le_rfl ⟨0, by omega⟩ n = p n := ⟨_, fun n => rfl⟩
  simp only [hp] at h44'
  obtain ⟨m0, hm0⟩ : ∃ n, p n ≠ 0 := by
    by_contra hc
    push Not at hc
    have := h44' i0
    simp [hc] at this
  obtain ⟨b, hb⟩ : ∃ b, σ b ≠ 0 := by
    rw [← hp m0, post_succ] at hm0
    exact ⟨_, hm0⟩
  set c : ℝ := σ a / σ b with hc
  set S : ℝ := ∑ i, ∑ n, dY i n * p n with hS
  set Q : ℝ := ∑ i : Fin (d (H' + 1 + 1)), ∑ n, p n ^ 2 with hQ
  have hSpos : 0 < S := Finset.sum_pos (fun i _ => h44' i) ⟨i0, Finset.mem_univ _⟩
  have hQnn : 0 ≤ Q := Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun n _ => sq_nonneg _))
  set t : ℝ := -S / (Q + 1) with ht
  refine ⟨thetaStar θ' hdH t c b, ?_⟩
  have hout' : ∀ i n, output σ X (thetaStar θ' hdH t c b) i n = t * p n + σ a := by
    intro i n
    unfold output
    have eL : (thetaStar θ' hdH t c b).1 (Fin.last (H' + 1)) =
        (fun (_ : Fin (d (H' + 1 + 1))) (j : Fin (d (H' + 1))) =>
          if j.val = 0 then t else if j.val = 1 then c else 0) := by
      simp only [thetaStar]
      rw [Function.update_of_ne]
      · exact Function.update_self _ _ _
      · intro h; have := congrArg Fin.val h; simp at this
    rw [eL]
    show ∑ j : Fin (d (H' + 1)), (if j.val = 0 then t else if j.val = 1 then c else 0) *
      post σ X (thetaStar θ' hdH t c b) (H' + 1) le_rfl j n = t * p n + σ a
    have hne : (⟨0, by omega⟩ : Fin (d (H' + 1))) ≠ ⟨1, by omega⟩ := by
      intro h; have := congrArg Fin.val h; simp at this
    rw [Finset.sum_eq_add_of_mem (⟨0, by omega⟩ : Fin (d (H' + 1))) ⟨1, by omega⟩
      (Finset.mem_univ _) (Finset.mem_univ _) hne]
    · obtain ⟨e0, e1⟩ := post_top σ X θ' hdH t c b n
      simp only [e0, e1, hp, if_true, one_ne_zero, if_false]
      rw [hc, div_mul_cancel₀ _ hb]
    · intro j _ hj
      have h0 : j.val ≠ 0 := fun h => hj.1 (Fin.ext h)
      have h1 : j.val ≠ 1 := fun h => hj.2 (Fin.ext h)
      simp [h0, h1]
  have hloss' : loss σ X (fun i n => σ a - dY i n) (thetaStar θ' hdH t c b) =
      ∑ i, ∑ n, dY i n ^ 2 + 2 * t * S + t ^ 2 * Q := by
    unfold loss
    simp only [hout', hS, hQ, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro n _
    ring
  rw [hloss']
  have hQ1 : 0 < Q + 1 := by linarith
  have key : 2 * t * S + t ^ 2 * Q < 0 := by
    have e : 2 * t * S + t ^ 2 * Q = -(S ^ 2 * (Q + 2)) / (Q + 1) ^ 2 := by
      rw [ht]; field_simp; ring
    rw [e]
    apply div_neg_of_neg_of_pos _ (by positivity)
    have : 0 < S ^ 2 * (Q + 2) := by positivity
    linarith
  linarith
