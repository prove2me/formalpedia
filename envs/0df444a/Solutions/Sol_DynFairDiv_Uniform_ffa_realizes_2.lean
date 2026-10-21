-- Prove2me | solution 2 for DynFairDiv.Uniform.ffa_realizes
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T15:41:10.371589+00:00
-- url     : https://prove2.me/submissions/85cbc3a7-5e86-4f37-91b8-7b96e7f857a1

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

/-- state of the realization: the list of users ordered by (nonincreasing) share, and the shares -/
noncomputable def realState (ψ : ℕ → ℕ) (σ : ℝ) : ℕ → List ℕ × (ℕ → ℝ)
  | 0 => ([], fun _ => 0)
  | t + 1 =>
    let π := (realState ψ σ t).1
    let v := (realState ψ σ t).2
    let m := min (ψ (t + 1)) t
    (π.drop m ++ π.take m ++ [t],
      fun k => if k = t ∨ k ∈ π.take m then σ / ((t + 1 : ℕ) : ℝ) else v k)

theorem realState_inv (ψ : ℕ → ℕ) (σ : ℝ) (t : ℕ) :
    (realState ψ σ t).1.Perm (List.range t) ∧
      (realState ψ σ t).1.map (realState ψ σ t).2 = ffa ψ σ t := by
  induction t with
  | zero => simp [realState, ffa]
  | succ t ih =>
    obtain ⟨hp, hm⟩ := ih
    set π := (realState ψ σ t).1 with hπ
    set v := (realState ψ σ t).2 with hv
    have hlen : π.length = t := by rw [hp.length_eq]; simp
    have hnd : π.Nodup := hp.nodup_iff.2 (List.nodup_range)
    have hmem : ∀ k ∈ π, k < t := fun k hk => List.mem_range.1 (hp.subset hk)
    have hrs : realState ψ σ (t + 1) =
        (π.drop (min (ψ (t + 1)) t) ++ π.take (min (ψ (t + 1)) t) ++ [t],
          fun k => if k = t ∨ k ∈ π.take (min (ψ (t + 1)) t) then σ / ((t + 1 : ℕ) : ℝ) else v k) := rfl
    rw [hrs]
    set m := min (ψ (t + 1)) t with hmdef
    have hmle : m ≤ t := min_le_right _ _
    constructor
    · -- permutation
      have : (π.drop m ++ π.take m ++ [t]).Perm (π ++ [t]) := by
        refine List.Perm.append_right _ ?_
        exact List.perm_append_comm.trans (by rw [List.take_append_drop])
      refine this.trans ?_
      rw [List.range_succ]
      exact hp.append_right _
    · simp only
      have hdisj : ∀ k ∈ π.drop m, k ≠ t ∧ k ∉ π.take m := by
        intro k hk
        refine ⟨(hmem k (List.mem_of_mem_drop hk)).ne, ?_⟩
        intro hk2
        have := List.disjoint_take_drop hnd (le_refl m)
        exact this hk2 hk
      rw [List.map_append, List.map_append]
      have h1 : (π.drop m).map (fun k => if k = t ∨ k ∈ π.take m then σ / ((t + 1 : ℕ) : ℝ) else v k)
          = (π.drop m).map v := by
        apply List.map_congr_left
        intro k hk
        have := hdisj k hk
        simp [this.1, this.2]
      have h2 : (π.take m).map (fun k => if k = t ∨ k ∈ π.take m then σ / ((t + 1 : ℕ) : ℝ) else v k)
          = List.replicate m (σ / ((t + 1 : ℕ) : ℝ)) := by
        have : (π.take m).length = m := by simp [hlen]; omega
        rw [List.map_congr_left (g := fun _ => σ / ((t + 1 : ℕ) : ℝ))
          (fun k hk => by simp [hk]), List.map_const', this]
      rw [h1, h2, List.map_drop, hm, ffa]
      have hd : (ffa ψ σ t).drop (ψ (t + 1)) = (ffa ψ σ t).drop m := by
        rw [hmdef]
        rcases le_total (ψ (t + 1)) t with h | h
        · rw [min_eq_left h]
        · rw [min_eq_right h]
          rw [List.drop_eq_nil_of_le (by rw [ffa_length]; exact h),
              List.drop_eq_nil_of_le (by rw [ffa_length])]
      rw [hd]
      simp only [List.map_cons, List.map_nil, ite_true, true_or]
      rw [List.replicate_succ', List.append_assoc]

theorem solution (ψ : ℕ → ℕ) (n : ℕ∞) (σ : ℝ) (hσ : 0 ≤ σ)
    (hfeas : ∀ t : ℕ, 1 ≤ t → (t : ℕ∞) ≤ n → ffaTotal ψ σ t ≤ 1) :
    ∃ X, AchievesRatio ψ n σ X ∧
      ∀ t : ℕ, 1 ≤ t → (t : ℕ∞) ≤ n →
        (List.ofFn (fun k : Fin t => X t k.val)).Perm (ffa ψ σ t) := by
  have hmemv : ∀ t k : ℕ, k < t → σ / (t : ℝ) ≤ (realState ψ σ t).2 k := by
    intro t k hk
    obtain ⟨hp, hm⟩ := realState_inv ψ σ t
    have hk' : k ∈ (realState ψ σ t).1 := hp.symm.subset (List.mem_range.2 hk)
    have : (realState ψ σ t).2 k ∈ ffa ψ σ t := by
      rw [← hm]; exact List.mem_map_of_mem hk'
    exact ffa_mem_ge ψ σ hσ t _ this
  have hsum : ∀ t, ∑ k ∈ Finset.range t, (realState ψ σ t).2 k = ffaTotal ψ σ t := by
    intro t
    obtain ⟨hp, hm⟩ := realState_inv ψ σ t
    have h1 : ∀ (f : ℕ → ℝ) (t : ℕ), ∑ k ∈ Finset.range t, f k = ((List.range t).map f).sum := by
      intro f t
      induction t with
      | zero => simp
      | succ t ih => rw [Finset.sum_range_succ, ih, List.range_succ, List.map_append, List.sum_append]; simp
    rw [h1, ffaTotal, ← hm]
    exact (hp.symm.map _).sum_eq
  refine ⟨fun t => (realState ψ σ t).2, ⟨fun t ht1 htn => ⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · intro k hk
    exact le_trans (div_nonneg hσ (Nat.cast_nonneg _)) (hmemv t k hk)
  · rw [hsum]; exact hfeas t ht1 htn
  · intro h2
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have hrs : realState ψ σ (s + 1) =
        ((realState ψ σ s).1.drop (min (ψ (s + 1)) s) ++
            (realState ψ σ s).1.take (min (ψ (s + 1)) s) ++ [s],
          fun k => if k = s ∨ k ∈ (realState ψ σ s).1.take (min (ψ (s + 1)) s)
            then σ / ((s + 1 : ℕ) : ℝ) else (realState ψ σ s).2 k) := rfl
    have hsub : (Finset.range s).filter (fun k => (realState ψ σ (s + 1)).2 k < (realState ψ σ s).2 k)
        ⊆ ((realState ψ σ s).1.take (min (ψ (s + 1)) s)).toFinset := by
      intro k hk
      rw [Finset.mem_filter, Finset.mem_range] at hk
      rw [List.mem_toFinset]
      by_contra hnot
      rw [hrs] at hk
      simp only [hnot, or_false, hk.1.ne] at hk
      simp at hk
    refine (Finset.card_le_card hsub).trans ?_
    refine (List.toFinset_card_le _).trans ?_
    rw [List.length_take]
    exact (min_le_left _ _).trans (min_le_left _ _)
  · intro t ht1 htn k hk
    exact hmemv t k hk
  · intro t ht1 htn
    have h1 : List.ofFn (fun k : Fin t => (realState ψ σ t).2 k.val) =
        (List.range t).map (realState ψ σ t).2 := by
      apply List.ext_getElem
      · simp
      · intro i h1 h2
        simp
    obtain ⟨hp, hm⟩ := realState_inv ψ σ t
    rw [h1, ← hm]
    exact (hp.symm.map _)
