-- Prove2me | solution 1 for DynFairDiv.Uniform.ffa_realizes
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T12:14:28.30823+00:00
-- url     : https://prove2.me/submissions/6ec48dec-83e7-45b2-a848-a517c3af22ce

import Mathlib
import Definitions.Def_DynFairDiv_Uniform_Model

open DynFairDiv.Uniform Finset

/-- The users ordered by their current FFA share (front = largest share). -/
private def ord (ψ : ℕ → ℕ) : ℕ → List ℕ
  | 0 => []
  | t + 1 => (ord ψ t).drop (ψ (t + 1)) ++ (ord ψ t).take (ψ (t + 1)) ++ [t]

/-- The user-labelled FFA shares. -/
private noncomputable def g (ψ : ℕ → ℕ) (σ : ℝ) : ℕ → ℕ → ℝ
  | 0 => fun _ => 0
  | t + 1 => fun k => if k ∈ (ord ψ t).take (ψ (t + 1)) ∨ k = t then σ / ((t + 1 : ℕ) : ℝ)
      else g ψ σ t k

private lemma ord_perm (ψ : ℕ → ℕ) (t : ℕ) : (ord ψ t).Perm (List.range t) := by
  induction t with
  | zero => simp [ord]
  | succ t ih =>
    rw [ord, List.range_succ]
    refine List.Perm.append_right [t] ?_
    exact (List.perm_append_comm.trans (by rw [List.take_append_drop])).trans ih

private lemma ord_nodup (ψ : ℕ → ℕ) (t : ℕ) : (ord ψ t).Nodup :=
  (ord_perm ψ t).nodup_iff.mpr List.nodup_range

private lemma mem_ord (ψ : ℕ → ℕ) (t k : ℕ) : k ∈ ord ψ t ↔ k < t := by
  rw [(ord_perm ψ t).mem_iff, List.mem_range]

private lemma ord_len (ψ : ℕ → ℕ) (t : ℕ) : (ord ψ t).length = t := by
  rw [(ord_perm ψ t).length_eq, List.length_range]

private lemma map_g (ψ : ℕ → ℕ) (σ : ℝ) (t : ℕ) : (ord ψ t).map (g ψ σ t) = ffa ψ σ t := by
  induction t with
  | zero => simp [ord, ffa]
  | succ t ih =>
    have hnd : ((ord ψ t).take (ψ (t + 1)) ++ (ord ψ t).drop (ψ (t + 1))).Nodup := by
      rw [List.take_append_drop]; exact ord_nodup ψ t
    have hdisj := (List.nodup_append.mp hnd).2.2
    rw [ord, ffa, ← ih, List.map_append, List.map_append, List.map_drop,
      List.replicate_succ', ← List.append_assoc]
    congr 1
    · congr 1
      · rw [← List.map_drop, ← List.map_drop]
        apply List.map_congr_left
        intro k hk
        have hk1 : k ∉ (ord ψ t).take (ψ (t + 1)) := fun h => hdisj k h k hk rfl
        have hk2 : k ≠ t := by
          have := (mem_ord ψ t k).mp (List.mem_of_mem_drop hk); omega
        simp [g, hk1, hk2]
      · rw [List.eq_replicate_iff]
        refine ⟨by rw [List.length_map, List.length_take, ord_len], ?_⟩
        intro b hb
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hb
        simp [g, hk]
    · simp [g]

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

private lemma g_mem (ψ : ℕ → ℕ) (σ : ℝ) (t k : ℕ) (hk : k < t) : g ψ σ t k ∈ ffa ψ σ t := by
  rw [← map_g]
  exact List.mem_map_of_mem ((mem_ord ψ t k).mpr hk)

private lemma ofFn_eq (t : ℕ) (f : ℕ → ℝ) :
    List.ofFn (fun k : Fin t => f k.val) = (List.range t).map f :=
  List.ext_getElem (by simp) (by simp)

theorem solution (ψ : ℕ → ℕ) (n : ℕ∞) (σ : ℝ) (hσ : 0 ≤ σ)
    (hfeas : ∀ t : ℕ, 1 ≤ t → (t : ℕ∞) ≤ n → ffaTotal ψ σ t ≤ 1) :
    ∃ X, AchievesRatio ψ n σ X ∧
      ∀ t : ℕ, 1 ≤ t → (t : ℕ∞) ≤ n →
        (List.ofFn (fun k : Fin t => X t k.val)).Perm (ffa ψ σ t) := by
  have hperm : ∀ t, (List.ofFn (fun k : Fin t => g ψ σ t k.val)).Perm (ffa ψ σ t) := by
    intro t
    rw [ofFn_eq, ← map_g]
    exact ((ord_perm ψ t).map _).symm
  have hlb : ∀ t k : ℕ, k < t → σ / (t : ℝ) ≤ g ψ σ t k :=
    fun t k hk => ffa_lb ψ σ hσ t _ (g_mem ψ σ t k hk)
  refine ⟨g ψ σ, ⟨?_, fun t _ _ k hk => hlb t k hk⟩, fun t _ _ => hperm t⟩
  intro t ht htn
  refine ⟨fun k hk => le_trans (by positivity) (hlb t k hk), ?_, ?_⟩
  · have : ∑ k ∈ range t, g ψ σ t k = ffaTotal ψ σ t := by
      rw [Finset.sum_range, ← List.sum_ofFn, ffaTotal]
      exact (hperm t).sum_eq
    rw [this]; exact hfeas t ht htn
  · intro ht2
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    calc ((range s).filter (fun k => g ψ σ (s + 1) k < g ψ σ s k)).card
        ≤ ((ord ψ s).take (ψ (s + 1))).toFinset.card := by
          apply Finset.card_le_card
          intro k hk
          rw [Finset.mem_filter, Finset.mem_range] at hk
          rw [List.mem_toFinset]
          by_contra hcon
          have hks : k ≠ s := by omega
          have : g ψ σ (s + 1) k = g ψ σ s k := by simp [g, hcon, hks]
          linarith [hk.2]
      _ ≤ ((ord ψ s).take (ψ (s + 1))).length := List.toFinset_card_le _
      _ ≤ ψ (s + 1) := by rw [List.length_take]; omega
