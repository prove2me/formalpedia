-- Prove2me | solution 2 for DynFairDiv.Uniform.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T15:38:10.295958+00:00
-- url     : https://prove2.me/submissions/4d1ef47f-7e1f-4fbf-a581-5459650189a2

import Mathlib
import Definitions.Def_DynFairDiv_Uniform_Model

set_option autoImplicit false
open DynFairDiv.Uniform

theorem ffa_length (ψ : ℕ → ℕ) (σ : ℝ) (t : ℕ) : (ffa ψ σ t).length = t := by
  induction t with
  | zero => simp [ffa]
  | succ t ih =>
    rw [ffa, List.length_append, List.length_drop, ih, List.length_replicate]
    omega

theorem ffa_mem_ge (ψ : ℕ → ℕ) (σ : ℝ) (hσ : 0 ≤ σ) (t : ℕ) :
    ∀ x ∈ ffa ψ σ t, σ / (t : ℝ) ≤ x := by
  induction t with
  | zero => simp [ffa]
  | succ t ih =>
    intro x hx
    rw [ffa, List.mem_append] at hx
    rcases hx with hx | hx
    · have h1 := ih x (List.mem_of_mem_drop hx)
      have h2 : σ / ((t + 1 : ℕ) : ℝ) ≤ σ / (t : ℝ) := by
        rcases Nat.eq_zero_or_pos t with h0 | hpos
        · subst h0; simp [ffa] at hx
        · apply div_le_div_of_nonneg_left hσ (by exact_mod_cast hpos)
          push_cast; linarith
      exact h2.trans h1
    · rw [List.eq_of_mem_replicate hx]

theorem ffa_sorted (ψ : ℕ → ℕ) (σ : ℝ) (hσ : 0 ≤ σ) (t : ℕ) :
    (ffa ψ σ t).Pairwise (· ≥ ·) := by
  induction t with
  | zero => simp [ffa]
  | succ t ih =>
    rw [ffa, List.pairwise_append]
    refine ⟨ih.sublist (List.drop_sublist _ _), ?_, ?_⟩
    · exact List.pairwise_replicate.2 (Or.inr le_rfl)
    · intro a ha b hb
      rw [List.eq_of_mem_replicate hb]
      have h1 := ffa_mem_ge ψ σ hσ t a (List.mem_of_mem_drop ha)
      have h2 : σ / ((t + 1 : ℕ) : ℝ) ≤ σ / (t : ℝ) := by
        rcases Nat.eq_zero_or_pos t with h0 | hpos
        · subst h0; simp [ffa] at ha
        · apply div_le_div_of_nonneg_left hσ (by exact_mod_cast hpos)
          push_cast; linarith
      exact h2.trans h1

/-- counting lemma: for a nonincreasing list, dropping `k` entries lowers the count of
entries `≥ x` by `k` (truncated). -/
theorem countP_drop_sorted (x : ℝ) : ∀ (F : List ℝ) (k : ℕ), F.Pairwise (· ≥ ·) →
    (F.drop k).countP (fun y => decide (x ≤ y)) = F.countP (fun y => decide (x ≤ y)) - k := by
  intro F
  induction F with
  | nil => intro k _; simp
  | cons a F ih =>
    intro k hp
    rcases k with _ | k
    · simp
    · rw [List.pairwise_cons] at hp
      by_cases hax : x ≤ a
      · rw [List.drop_succ_cons, ih k hp.2, List.countP_cons_of_pos (by simpa using hax)]
        omega
      · have h0 : F.countP (fun y => decide (x ≤ y)) = 0 := by
          rw [List.countP_eq_zero]
          intro y hy
          have := hp.1 y hy
          simp; linarith [not_le.1 hax]
        have h1 : (F.drop k).countP (fun y => decide (x ≤ y)) = 0 := by
          rw [List.countP_eq_zero]
          intro y hy
          have := hp.1 y (List.mem_of_mem_drop hy)
          simp; linarith [not_le.1 hax]
        rw [List.drop_succ_cons, h1, List.countP_cons_of_neg (by simpa using hax), h0]
        simp

/-- domination of a nonincreasing list by a family, in terms of counts, implies domination of sums -/
theorem dom_sum : ∀ (F : List ℝ) (s : Finset ℕ) (Y : ℕ → ℝ), F.Pairwise (· ≥ ·) →
    (∀ k ∈ s, 0 ≤ Y k) →
    (∀ x : ℝ, F.countP (fun y => decide (x ≤ y)) ≤ (s.filter (fun k => x ≤ Y k)).card) →
    F.sum ≤ ∑ k ∈ s, Y k := by
  intro F
  induction F with
  | nil =>
    intro s Y _ hY _
    simpa using Finset.sum_nonneg hY
  | cons a F ih =>
    intro s Y hp hY hc
    rw [List.pairwise_cons] at hp
    have h1 := hc a
    rw [List.countP_cons_of_pos (by simp)] at h1
    have hne : (s.filter (fun k => a ≤ Y k)).Nonempty := by
      rw [← Finset.card_pos]; omega
    obtain ⟨k, hk⟩ := hne
    rw [Finset.mem_filter] at hk
    have hsum : ∑ j ∈ s, Y j = Y k + ∑ j ∈ s.erase k, Y j := by
      rw [Finset.add_sum_erase _ _ hk.1]
    rw [List.sum_cons, hsum]
    have := ih (s.erase k) Y hp.2 (fun j hj => hY j (Finset.mem_of_mem_erase hj)) ?_
    · linarith [hk.2]
    · intro x
      by_cases hax : x ≤ a
      · have h2 := hc x
        rw [List.countP_cons_of_pos (by simpa using hax)] at h2
        have h3 : (s.filter (fun j => x ≤ Y j)).card =
            ((s.erase k).filter (fun j => x ≤ Y j)).card + 1 := by
          have : (s.erase k).filter (fun j => x ≤ Y j) = (s.filter (fun j => x ≤ Y j)).erase k := by
            ext j; simp [Finset.mem_filter, Finset.mem_erase]; tauto
          rw [this, Finset.card_erase_add_one]
          rw [Finset.mem_filter]; exact ⟨hk.1, hax.trans hk.2⟩
        omega
      · have h0 : F.countP (fun y => decide (x ≤ y)) = 0 := by
          rw [List.countP_eq_zero]
          intro y hy
          have := hp.1 y hy
          simp; linarith [not_le.1 hax]
        rw [h0]; exact Nat.zero_le _

theorem solution (ψ : ℕ → ℕ) (n : ℕ∞) (σ : ℝ) (X : ℕ → ℕ → ℝ)
    (hσ : 0 ≤ σ) (hX : AchievesRatio ψ n σ X) :
    ∀ t : ℕ, 1 ≤ t → (t : ℕ∞) ≤ n →
      (∀ x ∈ ffa ψ σ t, 0 ≤ x) ∧ ffaTotal ψ σ t ≤ 1 := by
  obtain ⟨hf, hr⟩ := hX
  have key : ∀ t : ℕ, (t : ℕ∞) ≤ n → ∀ x : ℝ,
      (ffa ψ σ t).countP (fun y => decide (x ≤ y)) ≤
        ((Finset.range t).filter (fun k => x ≤ X t k)).card := by
    intro t
    induction t with
    | zero => intro _ x; simp [ffa]
    | succ t ih =>
      intro htn x
      have htn' : (t : ℕ∞) ≤ n := le_trans (by exact_mod_cast Nat.le_succ t) htn
      have ih := ih htn' x
      have h1 : 1 ≤ t + 1 := by omega
      obtain ⟨hnn, -, hdis⟩ := hf (t + 1) h1 htn
      have hD : ((Finset.range t).filter (fun k => X (t + 1) k < X t k)).card ≤ ψ (t + 1) := by
        rcases t with _ | t
        · simp
        · have := hdis (by omega)
          simpa using this
      rw [ffa, List.countP_append]
      by_cases hxc : x ≤ σ / ((t + 1 : ℕ) : ℝ)
      · have hall : (Finset.range (t + 1)).filter (fun k => x ≤ X (t + 1) k) = Finset.range (t + 1) := by
          apply Finset.filter_true_of_mem
          intro k hk
          exact hxc.trans (hr (t + 1) h1 htn k (Finset.mem_range.1 hk))
        rw [hall, Finset.card_range]
        have hl := ffa_length ψ σ (t + 1)
        rw [ffa, List.length_append] at hl
        have := List.countP_le_length (p := fun y => decide (x ≤ y)) (l := (ffa ψ σ t).drop (ψ (t + 1)))
        have := List.countP_le_length (p := fun y => decide (x ≤ y))
          (l := List.replicate (min (ψ (t + 1)) t + 1) (σ / ((t + 1 : ℕ) : ℝ)))
        omega
      · have hrep : (List.replicate (min (ψ (t + 1)) t + 1) (σ / ((t + 1 : ℕ) : ℝ))).countP
            (fun y => decide (x ≤ y)) = 0 := by
          rw [List.countP_eq_zero]
          intro y hy
          rw [List.eq_of_mem_replicate hy]
          simpa using hxc
        rw [hrep, Nat.add_zero, countP_drop_sorted x _ _ (ffa_sorted ψ σ hσ t)]
        set A := (Finset.range t).filter (fun k => x ≤ X t k) with hA
        set D := (Finset.range t).filter (fun k => X (t + 1) k < X t k) with hDdef
        have hsub : A \ D ⊆ (Finset.range (t + 1)).filter (fun k => x ≤ X (t + 1) k) := by
          intro k hk
          rw [Finset.mem_sdiff, hA, hDdef, Finset.mem_filter, Finset.mem_filter] at hk
          obtain ⟨⟨hkr, hkx⟩, hkd⟩ := hk
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_range.2 (Nat.lt_succ_of_lt (Finset.mem_range.1 hkr)), ?_⟩
          have : ¬ (X (t + 1) k < X t k) := fun h => hkd ⟨hkr, h⟩
          linarith [not_lt.1 this]
        have h2 := Finset.card_le_card hsub
        have h3 := Finset.le_card_sdiff D A
        omega
  intro t ht1 htn
  have hlen := ffa_length ψ σ t
  have hnn : ∀ x ∈ ffa ψ σ t, 0 ≤ x := fun x hx =>
    le_trans (div_nonneg hσ (Nat.cast_nonneg _)) (ffa_mem_ge ψ σ hσ t x hx)
  refine ⟨hnn, ?_⟩
  have hfin := dom_sum (ffa ψ σ t) (Finset.range t) (X t) (ffa_sorted ψ σ hσ t)
    (fun k hk => (hf t ht1 htn).1 k (Finset.mem_range.1 hk)) (key t htn)
  exact hfin.trans (hf t ht1 htn).2.1
