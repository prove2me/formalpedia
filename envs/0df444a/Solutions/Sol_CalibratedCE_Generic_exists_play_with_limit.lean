-- Prove2me | solution 1 for CalibratedCE.Generic.exists_play_with_limit
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:12:45.453029+00:00
-- url     : https://prove2.me/submissions/5a4586da-9343-4115-9805-a1daf840a0cd

import Mathlib
import Definitions.Def_CalibratedCE_Generic_Game

open Filter Topology

namespace CalibratedCE.Generic

/-- Greedy selection: a maximizer of `v s + p s`. -/
noncomputable def aux_epl_sel {α : Type} [Fintype α] [Nonempty α] (p : α → ℝ) (v : α → ℝ) : α :=
  Classical.choose (Finite.exists_max (fun s => v s + p s))

lemma aux_epl_sel_spec {α : Type} [Fintype α] [Nonempty α] (p : α → ℝ) (v : α → ℝ) (s : α) :
    v s + p s ≤ v (aux_epl_sel p v) + p (aux_epl_sel p v) :=
  Classical.choose_spec (Finite.exists_max (fun s => v s + p s)) s

/-- The deficit vector `t * p s - count_t s` of the greedy sequence. -/
noncomputable def aux_epl_err {α : Type} [Fintype α] [Nonempty α] [DecidableEq α]
    (p : α → ℝ) : ℕ → α → ℝ
  | 0 => fun _ => 0
  | t + 1 => fun s =>
      aux_epl_err p t s + p s - if s = aux_epl_sel p (aux_epl_err p t) then 1 else 0

lemma aux_epl_err_sum {α : Type} [Fintype α] [Nonempty α] [DecidableEq α] (p : α → ℝ)
    (hp1 : ∑ a, p a = 1) (t : ℕ) : ∑ s, aux_epl_err p t s = 0 := by
  induction t with
  | zero => simp [aux_epl_err]
  | succ t ih =>
    simp only [aux_epl_err]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ih, hp1, Finset.sum_ite_eq']
    simp

lemma aux_epl_sel_pos {α : Type} [Fintype α] [Nonempty α] (p : α → ℝ)
    (hp1 : ∑ a, p a = 1) (v : α → ℝ) (hv : ∑ s, v s = 0) :
    0 < v (aux_epl_sel p v) + p (aux_epl_sel p v) := by
  have h1 : ∑ s, (v s + p s) = 1 := by rw [Finset.sum_add_distrib, hv, hp1]; ring
  have h2 : ∑ s, (v s + p s) ≤ ∑ _s : α, (v (aux_epl_sel p v) + p (aux_epl_sel p v)) :=
    Finset.sum_le_sum (fun s _ => aux_epl_sel_spec p v s)
  rw [h1, Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h2
  by_contra h
  rw [not_lt] at h
  have : (0:ℝ) ≤ Fintype.card α := Nat.cast_nonneg _
  nlinarith

lemma aux_epl_err_lower {α : Type} [Fintype α] [Nonempty α] [DecidableEq α] (p : α → ℝ)
    (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1) (t : ℕ) (s : α) : -1 < aux_epl_err p t s := by
  induction t generalizing s with
  | zero => simp [aux_epl_err]
  | succ t ih =>
    simp only [aux_epl_err]
    have hpos := aux_epl_sel_pos p hp1 (aux_epl_err p t) (aux_epl_err_sum p hp1 t)
    split_ifs with h
    · subst h; linarith
    · have := ih s; have := hp0 s; linarith

lemma aux_epl_err_zero {α : Type} [Fintype α] [Nonempty α] [DecidableEq α] (p : α → ℝ)
    (t : ℕ) (s : α) (hs : p s = 0) : aux_epl_err p t s ≤ 0 := by
  induction t with
  | zero => simp [aux_epl_err]
  | succ t ih =>
    simp only [aux_epl_err]
    split_ifs <;> linarith

lemma aux_epl_err_upper {α : Type} [Fintype α] [Nonempty α] [DecidableEq α] (p : α → ℝ)
    (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1) (t : ℕ) (s : α) :
    aux_epl_err p t s ≤ Fintype.card α := by
  have hsum : ∑ s, (aux_epl_err p t s + 1) = Fintype.card α := by
    rw [Finset.sum_add_distrib, aux_epl_err_sum p hp1 t]; simp
  have := Finset.single_le_sum (f := fun s => aux_epl_err p t s + 1)
    (fun i _ => by have := aux_epl_err_lower p hp0 hp1 t i; linarith) (Finset.mem_univ s)
  linarith

lemma aux_epl_count {α : Type} [Fintype α] [Nonempty α] [DecidableEq α] (p : α → ℝ)
    (t : ℕ) (a : α) :
    ((((Finset.range t).filter (fun i => aux_epl_sel p (aux_epl_err p i) = a)).card : ℕ) : ℝ)
      = t * p a - aux_epl_err p t a := by
  induction t with
  | zero => simp [aux_epl_err]
  | succ t ih =>
    rw [Finset.range_add_one, Finset.filter_insert]
    simp only [aux_epl_err]
    by_cases h : aux_epl_sel p (aux_epl_err p t) = a
    · rw [if_pos h, Finset.card_insert_of_notMem (by simp), Nat.cast_add, ih, if_pos h.symm]
      push_cast; ring
    · rw [if_neg h, ih, if_neg (Ne.symm h)]
      push_cast; ring

lemma aux_epl_main {α : Type} [Fintype α] [Nonempty α] [DecidableEq α] (p : α → ℝ)
    (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1) :
    ∃ z : ℕ → α, (∀ t, 0 < p (z t)) ∧ ∀ a,
      Tendsto (fun t : ℕ => (((Finset.range t).filter (fun i => z i = a)).card : ℝ) / t)
        atTop (𝓝 (p a)) := by
  refine ⟨fun i => aux_epl_sel p (aux_epl_err p i), ?_, ?_⟩
  · intro t
    have hpos := aux_epl_sel_pos p hp1 (aux_epl_err p t) (aux_epl_err_sum p hp1 t)
    rcases (hp0 (aux_epl_sel p (aux_epl_err p t))).lt_or_eq with h | h
    · exact h
    · have := aux_epl_err_zero p t _ h.symm
      linarith
  · intro a
    have hlim : Tendsto (fun t : ℕ => p a - aux_epl_err p t a / t) atTop (𝓝 (p a)) := by
      have h0 : Tendsto (fun t : ℕ => aux_epl_err p t a / t) atTop (𝓝 0) := by
        apply squeeze_zero_norm' _ (tendsto_const_div_atTop_nhds_zero_nat (Fintype.card α : ℝ))
        filter_upwards with t
        rw [Real.norm_eq_abs, abs_div, Nat.abs_cast]
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        rw [abs_le]
        constructor
        · have := aux_epl_err_lower p hp0 hp1 t a
          have : (1:ℝ) ≤ Fintype.card α := by exact_mod_cast Fintype.card_pos
          linarith
        · exact aux_epl_err_upper p hp0 hp1 t a
      simpa using (tendsto_const_nhds (x := p a)).sub h0
    refine Tendsto.congr' ?_ hlim
    filter_upwards [eventually_ge_atTop 1] with t ht
    show p a - aux_epl_err p t a / t =
      ((((Finset.range t).filter (fun i => aux_epl_sel p (aux_epl_err p i) = a)).card : ℕ) : ℝ) / t
    rw [aux_epl_count]
    have : (t:ℝ) ≠ 0 := by
      have : (1:ℝ) ≤ t := by exact_mod_cast ht
      linarith
    field_simp

end CalibratedCE.Generic

open CalibratedCE.Generic

theorem solution {m n : ℕ} (D : Fin m → Fin n → ℝ) (hD : IsJointDist D) :
    ∃ (x : ℕ → Fin m) (y : ℕ → Fin n), (∀ t, 0 < D (x t) (y t)) ∧
      ∀ a b, Tendsto (fun t => empDist x y t a b) atTop (𝓝 (D a b)) := by
  obtain ⟨h0, h1⟩ := hD
  have hsum : ∑ s : Fin m × Fin n, D s.1 s.2 = 1 := by
    rw [Fintype.sum_prod_type']; exact h1
  have hne : Nonempty (Fin m × Fin n) := by
    by_contra hc
    rw [not_nonempty_iff] at hc
    simp at hsum
  obtain ⟨z, hz, hlim⟩ :=
    aux_epl_main (fun s : Fin m × Fin n => D s.1 s.2) (fun s => h0 _ _) hsum
  refine ⟨fun t => (z t).1, fun t => (z t).2, hz, fun a b => ?_⟩
  have := hlim (a, b)
  simp only [Prod.ext_iff] at this
  exact this
