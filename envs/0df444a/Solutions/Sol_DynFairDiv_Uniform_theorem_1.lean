-- Prove2me | solution 1 for DynFairDiv.Uniform.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T12:10:07.376219+00:00
-- url     : https://prove2.me/submissions/04272abd-6280-48e2-a136-be23e063ceee

import Mathlib
import Definitions.Def_DynFairDiv_Uniform_Model

open DynFairDiv.Uniform Finset

/-- If every upper level set of `A` is no larger than that of `B` and `B ≥ 0`, then
`sum A ≤ sum B`. -/
private lemma msum_le_of_count (A B : Multiset ℝ) (hB : ∀ b ∈ B, 0 ≤ b)
    (h : ∀ c : ℝ, (A.filter (fun x => c ≤ x)).card ≤ (B.filter (fun x => c ≤ x)).card) :
    A.sum ≤ B.sum := by
  induction hn : A.card generalizing A B with
  | zero =>
    rw [Multiset.card_eq_zero] at hn
    subst hn
    simpa using Multiset.sum_nonneg hB
  | succ n ih =>
    have hA0 : A ≠ 0 := by intro h0; simp [h0] at hn
    obtain ⟨a0, ha0, hamax⟩ := Multiset.exists_max_image id hA0
    have hcB : 1 ≤ (B.filter (fun x => a0 ≤ x)).card := by
      refine le_trans ?_ (h a0)
      rw [Nat.one_le_iff_ne_zero, Ne, Multiset.card_eq_zero, Multiset.filter_eq_nil]
      simp only [not_forall, not_le]
      exact ⟨a0, ha0, fun h' => lt_irrefl _ h'⟩
    have hB0 : B ≠ 0 := by intro h0; simp [h0] at hcB
    obtain ⟨b0, hb0, hbmax⟩ := Multiset.exists_max_image id hB0
    have hab : a0 ≤ b0 := by
      obtain ⟨b, hb⟩ := Multiset.card_pos_iff_exists_mem.mp hcB
      rw [Multiset.mem_filter] at hb
      exact hb.2.trans (hbmax b hb.1)
    have eA := Multiset.cons_erase ha0
    have eB := Multiset.cons_erase hb0
    rw [← eA, ← eB, Multiset.sum_cons, Multiset.sum_cons]
    have := ih (A.erase a0) (B.erase b0)
      (fun b hb => hB b (Multiset.mem_of_mem_erase hb)) ?_ (by
        rw [Multiset.card_erase_of_mem ha0, hn]; rfl)
    · linarith
    · intro c
      by_cases hc : c ≤ a0
      · have h1 := h c
        rw [← eA, ← eB, Multiset.filter_cons_of_pos _ hc,
          Multiset.filter_cons_of_pos _ (hc.trans hab), Multiset.card_cons,
          Multiset.card_cons] at h1
        exact Nat.le_of_succ_le_succ h1
      · rw [Multiset.filter_eq_nil.mpr]
        · simp
        · intro x hx hcx
          exact hc (hcx.trans (hamax x (Multiset.mem_of_mem_erase hx)))

private lemma ffa_len (ψ : ℕ → ℕ) (σ : ℝ) (t : ℕ) : (ffa ψ σ t).length = t := by
  induction t with
  | zero => simp [ffa]
  | succ t ih => simp [ffa, ih]; try omega

private lemma ffa_lb (ψ : ℕ → ℕ) (σ : ℝ) (hσ : 0 ≤ σ) (t : ℕ) :
    ∀ x ∈ ffa ψ σ t, σ / (t : ℝ) ≤ x := by
  induction t with
  | zero => simp [ffa]
  | succ t ih =>
    intro x hx
    rw [ffa, List.mem_append] at hx
    rcases hx with hx | hx
    · have hx' := ih x (List.mem_of_mem_drop hx)
      rcases Nat.eq_zero_or_pos t with rfl | ht
      · simp [ffa] at hx
      · refine le_trans ?_ hx'
        apply div_le_div_of_nonneg_left hσ (by exact_mod_cast ht)
        push_cast; linarith
    · rw [List.eq_of_mem_replicate hx]

private lemma ffa_sorted (ψ : ℕ → ℕ) (σ : ℝ) (hσ : 0 ≤ σ) (t : ℕ) :
    (ffa ψ σ t).Pairwise (fun a b => b ≤ a) := by
  induction t with
  | zero => simp [ffa]
  | succ t ih =>
    rw [ffa, List.pairwise_append]
    refine ⟨ih.sublist (List.drop_sublist _ _), ?_, ?_⟩
    · exact List.pairwise_replicate.mpr (Or.inr (le_refl _))
    · intro a ha b hb
      rw [List.eq_of_mem_replicate hb]
      have ha' := ffa_lb ψ σ hσ t a (List.mem_of_mem_drop ha)
      rcases Nat.eq_zero_or_pos t with rfl | ht
      · simp [ffa] at ha
      · refine le_trans ?_ ha'
        apply div_le_div_of_nonneg_left hσ (by exact_mod_cast ht)
        push_cast; linarith

private lemma countP_drop_sorted (c : ℝ) :
    ∀ (L : List ℝ) (k : ℕ), L.Pairwise (fun a b => b ≤ a) →
      (L.drop k).countP (fun x => decide (c ≤ x)) = L.countP (fun x => decide (c ≤ x)) - k := by
  intro L
  induction L with
  | nil => simp
  | cons x L ih =>
    intro k hL
    rw [List.pairwise_cons] at hL
    cases k with
    | zero => simp
    | succ k =>
      rw [List.drop_succ_cons, ih k hL.2, List.countP_cons]
      by_cases hcx : c ≤ x
      · simp [hcx]; try omega
      · have h0 : L.countP (fun x => decide (c ≤ x)) = 0 := by
          rw [List.countP_eq_zero]
          intro y hy hcy
          exact hcx ((of_decide_eq_true hcy).trans (hL.1 y hy))
        simp [hcx, h0]

theorem solution (ψ : ℕ → ℕ) (n : ℕ∞) (σ : ℝ) (X : ℕ → ℕ → ℝ)
    (hσ : 0 ≤ σ) (hX : AchievesRatio ψ n σ X) :
    ∀ t : ℕ, 1 ≤ t → (t : ℕ∞) ≤ n →
      (∀ x ∈ ffa ψ σ t, 0 ≤ x) ∧ ffaTotal ψ σ t ≤ 1 := by
  obtain ⟨hF, hR⟩ := hX
  -- level-set domination invariant
  have inv : ∀ t : ℕ, (t : ℕ∞) ≤ n → ∀ c : ℝ,
      (ffa ψ σ t).countP (fun x => decide (c ≤ x)) ≤
        ((range t).filter (fun k => c ≤ X t k)).card := by
    intro t
    induction t with
    | zero => intro _ c; simp [ffa]
    | succ t ih =>
      intro htn c
      have htn' : (t : ℕ∞) ≤ n := le_trans (by exact_mod_cast Nat.le_succ t) htn
      by_cases hc : c ≤ σ / ((t + 1 : ℕ) : ℝ)
      · have h1 : ((range (t + 1)).filter (fun k => c ≤ X (t + 1) k)) = range (t + 1) := by
          apply Finset.filter_true_of_mem
          intro k hk
          exact hc.trans (by exact_mod_cast hR (t + 1) (by omega) htn k (Finset.mem_range.mp hk))
        rw [h1, Finset.card_range]
        calc _ ≤ (ffa ψ σ (t + 1)).length := List.countP_le_length
          _ = t + 1 := ffa_len ψ σ (t + 1)
      · push Not at hc
        rw [ffa, List.countP_append, countP_drop_sorted c _ _ (ffa_sorted ψ σ hσ t)]
        have h0 : (List.replicate (min (ψ (t + 1)) t + 1) (σ / ((t + 1 : ℕ) : ℝ))).countP
            (fun x => decide (c ≤ x)) = 0 := by
          rw [List.countP_eq_zero]
          intro y hy hcy
          rw [List.eq_of_mem_replicate hy] at hcy
          exact absurd (of_decide_eq_true hcy) (not_le.mpr hc)
        rw [h0, Nat.add_zero]
        rcases Nat.eq_zero_or_pos t with rfl | ht
        · simp [ffa]
        · have hdis := (hF (t + 1) (by omega) htn).2.2 (by omega)
          simp only [Nat.add_sub_cancel] at hdis
          have hsub : (range t).filter (fun k => c ≤ X t k) ⊆
              ((range (t + 1)).filter (fun k => c ≤ X (t + 1) k)) ∪
                ((range t).filter (fun k => X (t + 1) k < X t k)) := by
            intro k hk
            rw [Finset.mem_filter, Finset.mem_range] at hk
            rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter, Finset.mem_range,
              Finset.mem_range]
            by_cases hlt : X (t + 1) k < X t k
            · exact Or.inr ⟨hk.1, hlt⟩
            · exact Or.inl ⟨by omega, hk.2.trans (not_lt.mp hlt)⟩
          have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
          have := ih htn' c
          omega
  intro t ht htn
  refine ⟨fun x hx => le_trans (by positivity) (ffa_lb ψ σ hσ t x hx), ?_⟩
  have hsum : (ffa ψ σ t).sum ≤ ∑ k ∈ range t, X t k := by
    have := msum_le_of_count (↑(ffa ψ σ t)) ((range t).val.map (X t))
      (by
        intro b hb
        obtain ⟨k, hk, rfl⟩ := Multiset.mem_map.mp hb
        exact (hF t ht htn).1 k (Finset.mem_range.mp hk))
      (by
        intro c
        have := inv t htn c
        rw [Multiset.filter_map, Multiset.card_map, ← Multiset.countP_eq_card_filter,
          Multiset.coe_countP]
        exact this)
    simpa [Finset.sum_eq_multiset_sum] using this
  exact hsum.trans (hF t ht htn).2.1
