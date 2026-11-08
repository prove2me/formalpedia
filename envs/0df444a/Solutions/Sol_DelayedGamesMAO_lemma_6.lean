-- Prove2me | solution 1 for DelayedGamesMAO.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T17:42:19.764853+00:00
-- url     : https://prove2.me/submissions/10d6dba3-b5b1-4ba1-a199-5ebdf505c314

import Mathlib
import Definitions.Def_DelayedGamesMAO_IsAllocationSchedule
import Definitions.Def_DelayedGamesMAO_congAlloc

set_option autoImplicit false

namespace Aux_DGM6

open DelayedGamesMAO

theorem mem_active (d : ℕ → ℕ) (t k : ℕ) :
    k ∈ active d t ↔ k = t ∨ (1 ≤ k ∧ k ≤ t - 1 ∧ t ≤ k + d k) := by
  unfold active pending
  simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_Icc]
  tauto

theorem q_pos (d : ℕ → ℕ) (t : ℕ) : 1 ≤ q d t := by
  unfold q active
  exact Finset.card_pos.mpr (Finset.insert_nonempty _ _)

theorem q_le_kappa (d : ℕ → ℕ) (s t : ℕ) (h : s ≤ t) : q d t ≤ kappaRun d s t := by
  unfold kappaRun
  exact Finset.le_sup (Finset.mem_Icc.mpr ⟨h, le_rfl⟩)

theorem kappa_mono (d : ℕ → ℕ) (s k : ℕ) : kappaRun d s k ≤ kappaRun d s (k + 1) := by
  unfold kappaRun
  exact Finset.sup_mono (Finset.Icc_subset_Icc le_rfl (Nat.le_succ k))

end Aux_DGM6

open DelayedGamesMAO Aux_DGM6 in
theorem solution (T : ℕ) (hT : 1 ≤ T) (d : ℕ → ℕ) (hd : ∀ t ∈ Finset.Icc 1 T, t + d t ≤ T) :
    IsAllocationSchedule d T (congAlloc d) := by
  have hnn : ∀ t k, 0 ≤ congAlloc d t k := by
    intro t k
    unfold congAlloc
    split_ifs
    · positivity
    · exact le_rfl
  refine ⟨fun t _ k _ => hnn t k, fun t ht => ⟨?_, ?_, ?_, ?_⟩⟩
  · intro k hk
    rw [Finset.mem_Icc] at ht hk
    unfold congAlloc
    by_cases h1 : t ∈ active d (k + 1)
    · rw [if_pos h1]
      have h2 : t ∈ active d k := by
        rw [mem_active] at h1 ⊢
        rcases h1 with h | ⟨_, _, h⟩
        · omega
        · by_cases htk : t = k
          · left; exact htk
          · right; omega
      rw [if_pos h2]
      have hk1 : (1 : ℝ) ≤ (kappaRun d t k : ℝ) := by
        have := q_le_kappa d t k hk.1
        have := q_pos d k
        exact_mod_cast (by omega : 1 ≤ kappaRun d t k)
      have hmono : (kappaRun d t k : ℝ) ≤ (kappaRun d t (k + 1) : ℝ) := by
        exact_mod_cast kappa_mono d t k
      exact one_div_le_one_div_of_le (by linarith) hmono
    · rw [if_neg h1]
      exact hnn k t
  · intro k hk
    rw [Finset.mem_Icc] at ht hk
    unfold congAlloc
    rw [if_neg]
    rw [mem_active]
    omega
  · have hsub : active d t ⊆ Finset.Icc 1 t := by
      intro k hk
      rw [mem_active] at hk
      rw [Finset.mem_Icc] at ht ⊢
      omega
    symm
    apply Finset.sum_subset hsub
    intro k _ hk
    unfold congAlloc
    rw [if_neg hk]
  · rw [Finset.mem_Icc] at ht
    have hq := q_pos d t
    have hqR : (0 : ℝ) < (q d t : ℝ) := by exact_mod_cast hq
    calc ∑ k ∈ active d t, congAlloc d t k
        ≤ ∑ _k ∈ active d t, 1 / (q d t : ℝ) := by
          apply Finset.sum_le_sum
          intro k hk
          unfold congAlloc
          rw [if_pos hk]
          have hkt : k ≤ t := by rw [mem_active] at hk; omega
          have : (q d t : ℝ) ≤ (kappaRun d k t : ℝ) := by exact_mod_cast q_le_kappa d k t hkt
          exact one_div_le_one_div_of_le hqR this
      _ = 1 := by
          rw [Finset.sum_const, nsmul_eq_mul]
          unfold q at hqR ⊢
          field_simp
