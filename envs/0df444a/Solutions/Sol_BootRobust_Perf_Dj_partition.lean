-- Prove2me | solution 1 for BootRobust.Perf.Dj_partition
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:08:13.790458+00:00
-- url     : https://prove2.me/submissions/9eada85e-c8c2-4076-9b57-af0b9cd45aa7

import Mathlib
import Definitions.Def_BootRobust_Perf_Setting
set_option autoImplicit false
open BootRobust.Perf

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] (n k : ℕ) (hk : 1 ≤ k)
    (hkn : k ≤ n) (N : ℕ → Finset ι) (hNmono : Monotone N) (hN0 : N 0 = ∅)
    (hNn : N n = Finset.univ) :
    (∀ j ∈ Finset.Icc 1 n, ∀ j' ∈ Finset.Icc 1 n, j ≠ j' →
        Disjoint (Dj n k N j ∩ Dnn n) (Dj n k N j' ∩ Dnn n)) ∧
      (⋃ j ∈ Finset.Icc 1 n, Dj n k N j ∩ Dnn n) = Dnn n := by
  have hn : (0:ℝ) < n := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hmono : ∀ (D : ι → ℝ), (∀ i, 0 ≤ D i) → ∀ s t : Finset ι, s ⊆ t → mass D s ≤ mass D t := by
    intro D hD s t hst
    unfold mass
    exact Finset.sum_le_sum_of_subset_of_nonneg hst (fun i _ _ => hD i)
  have key : ∀ j j' : ℕ, j < j' → ∀ D : ι → ℝ, D ∈ Dj n k N j → D ∈ Dj n k N j' → False := by
    intro j j' hjj D h1 h2
    have hD0 : ∀ i, 0 ≤ D i := h1.1.1
    have h3 : mass D (N j) ≤ mass D (N (j' - 1)) := hmono D hD0 _ _ (hNmono (by omega))
    have h4 := h1.2.2
    have h5 := h2.2.1
    have h6 : (k:ℝ) / n ≤ ((k:ℝ) - 1) / n := le_trans h4 (le_trans h3 h5)
    rw [div_le_div_iff_of_pos_right hn] at h6
    linarith
  refine ⟨?_, ?_⟩
  · intro j _ j' _ hne
    rw [Set.disjoint_left]
    rintro D ⟨h1, _⟩ ⟨h2, _⟩
    rcases lt_or_gt_of_ne hne with h | h
    · exact key j j' h D h1 h2
    · exact key j' j h D h2 h1
  · ext D
    simp only [Set.mem_iUnion, Set.mem_inter_iff, exists_prop]
    constructor
    · rintro ⟨j, _, _, hD⟩; exact hD
    · intro hD
      have hDD := hD
      obtain ⟨hs, hm⟩ := hD
      have hD0 : ∀ i, 0 ≤ D i := hs.1
      have hsum : ∑ i, D i = 1 := hs.2
      choose m hmn hm using hm
      classical
      have hP : ∀ j, (k:ℝ) / n ≤ mass D (N j) → True := fun _ _ => trivial
      have hPn : (k:ℝ) / n ≤ mass D (N n) := by
        rw [hNn]
        show (k:ℝ) / n ≤ ∑ i, D i
        rw [hsum, div_le_one hn]
        exact_mod_cast hkn
      have hex : ∃ j, (k:ℝ) / n ≤ mass D (N j) := ⟨n, hPn⟩
      have hjP : (k:ℝ) / n ≤ mass D (N (Nat.find hex)) := Nat.find_spec hex
      have hj0 : Nat.find hex ≠ 0 := by
        intro h
        rw [h, hN0] at hjP
        have : mass D (∅ : Finset ι) = 0 := by simp [mass]
        rw [this] at hjP
        have : (0:ℝ) < (k:ℝ) / n := by
          have : (0:ℝ) < k := by exact_mod_cast hk
          positivity
        linarith
      have hjn : Nat.find hex ≤ n := Nat.find_min' hex hPn
      have hlt : ¬ ((k:ℝ) / n ≤ mass D (N (Nat.find hex - 1))) := Nat.find_min hex (by omega)
      push_neg at hlt
      have hnm : (n:ℝ) * mass D (N (Nat.find hex - 1)) = ((∑ i ∈ N (Nat.find hex - 1), m i : ℕ) : ℝ) := by
        unfold mass
        rw [Finset.mul_sum]
        push_cast
        exact Finset.sum_congr rfl (fun i _ => hm i)
      have hS : ((∑ i ∈ N (Nat.find hex - 1), m i : ℕ) : ℝ) < k := by
        rw [← hnm]
        rw [lt_div_iff₀ hn] at hlt
        linarith
      have hS' : (∑ i ∈ N (Nat.find hex - 1), m i) ≤ k - 1 := by
        have : (∑ i ∈ N (Nat.find hex - 1), m i) < k := by exact_mod_cast hS
        omega
      have hS'' : ((∑ i ∈ N (Nat.find hex - 1), m i : ℕ) : ℝ) ≤ (k:ℝ) - 1 := by
        have := (Nat.cast_le (α := ℝ)).2 hS'
        rw [Nat.cast_sub hk] at this
        simpa using this
      refine ⟨Nat.find hex, Finset.mem_Icc.2 ⟨by omega, hjn⟩, ⟨hs, ?_, hjP⟩, hDD⟩
      rw [le_div_iff₀ hn]
      linarith [hnm, hS'']
