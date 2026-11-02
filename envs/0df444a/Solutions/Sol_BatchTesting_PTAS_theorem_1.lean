-- Prove2me | solution 1 for BatchTesting.PTAS.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T18:13:07.339236+00:00
-- url     : https://prove2.me/submissions/7b7dd727-abc2-475f-a850-4c1e005b3b11

import Mathlib
import Definitions.Def_BatchTesting_PTAS_Model
import Theorems.Thm_BatchTesting_PTAS_rounding_sandwich
import Theorems.Thm_BatchTesting_PTAS_greedy_within_class
import Theorems.Thm_BatchTesting_PTAS_pathCost_eq_expectedCost
import Theorems.Thm_BatchTesting_PTAS_theorem_3
import Theorems.Thm_BatchTesting_PTAS_card_FGreat_le

open BatchTesting.PTAS

namespace BTThm1Aux

/-- A path of the DP restricted to `G` has no repeated states. -/
theorem path_nodup {n : ℕ} (I : Instance n) (eps : ℝ) (G : Finset (State I eps))
    (π : List (State I eps)) (hπ : IsPath I eps G π) : π.Nodup := by
  have h1 : π.IsChain (fun N M : State I eps => N < M) :=
    hπ.2.2.2.imp (fun a b h => lt_of_le_of_ne h.1 h.2)
  have h2 : π.Pairwise (fun N M : State I eps => N < M) := List.isChain_iff_pairwise.mp h1
  exact h2.imp (fun h => ne_of_lt h)

/-- If the DP restricted to `G` has a path, it has an optimal path (finitely many paths). -/
theorem exists_optPath {n : ℕ} (I : Instance n) (eps : ℝ) (G : Finset (State I eps))
    (h : ∃ π, IsPath I eps G π) : ∃ π, IsOptPath I eps G π := by
  classical
  let L : Finset (List (State I eps)) :=
    (G.powerset.biUnion fun s => s.val.lists.toFinset).filter (IsPath I eps G)
  have hmem : ∀ π, IsPath I eps G π → π ∈ L := by
    intro π hπ
    simp only [L, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_powerset]
    refine ⟨⟨π.toFinset, ?_, ?_⟩, hπ⟩
    · intro x hx
      exact hπ.2.2.1 x (List.mem_toFinset.mp hx)
    · rw [Multiset.mem_toFinset, Multiset.mem_lists_iff, List.toFinset_val, (path_nodup I eps G π hπ).dedup]
      rfl
  obtain ⟨π0, hπ0⟩ := h
  have hne : L.Nonempty := ⟨π0, hmem π0 hπ0⟩
  obtain ⟨π, hπL, hmin⟩ := L.exists_min_image (pathCost I eps) hne
  refine ⟨π, (Finset.mem_filter.mp hπL).2, fun π' hπ' => hmin π' (hmem π' hπ')⟩

end BTThm1Aux

open BTThm1Aux in
theorem solution {n : ℕ} (I : Instance n) (hI : I.Standing) (eps : ℝ) (h0 : 0 < eps) (h1 : eps ≤ 1) :
    (∃ π, IsOptPath I eps (FGreat I eps) π) ∧
      (∀ π, IsOptPath I eps (FGreat I eps) π →
        IsTestingScheme (schemeOf I eps π) ∧
          ∀ S, IsTestingScheme S →
            expectedCost I (schemeOf I eps π) ≤ (1 + eps) * K eps * expectedCost I S) ∧
      (FGreat I eps).card ≤ (n + 1) * (R I eps + ⌈Real.logb (1 + eps) (n : ℝ)⌉₊ + 1) *
        Nat.choose (⌊3 * (kappa n eps : ℝ) / eps ^ 2⌋₊ + (kappa n eps).toNat) (kappa n eps).toNat := by
  classical
  obtain ⟨hn, hp, hc, hb⟩ := hI
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hcmin : 0 ≤ cmin I := le_ciInf (fun i => (hc i).le)
  have hK : 0 ≤ K eps := by unfold K; positivity
  have hGF : FGreat I eps ⊆ F I eps := by
    unfold FGreat; exact Finset.filter_subset _ _
  -- the two-state path `0 → N^(all)` in `F`
  have hpath0 : IsPath I eps (F I eps) [0, Nall I eps] := by
    have h0F : (0 : State I eps) ∈ F I eps := by
      simp [F, Fintype.mem_piFinset]
    have hallF : Nall I eps ∈ F I eps := by
      simp [F, Fintype.mem_piFinset, Nall]
    have hne : (0 : State I eps) ≠ Nall I eps := by
      intro h
      have i : Fin n := ⟨0, hn⟩
      have hi : i ∈ cls I eps (classOf I eps i) := by simp [cls]
      have := congrFun h (classIdx I eps i)
      simp only [Pi.zero_apply, Nall, classIdx] at this
      exact (Finset.card_pos.mpr ⟨i, hi⟩).ne' this.symm
    refine ⟨rfl, rfl, ?_, ?_⟩
    · intro N hN
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hN
      rcases hN with rfl | rfl
      · exact h0F
      · exact hallF
    · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]
      exact ⟨fun r => Nat.zero_le _, hne⟩
  have hI' : I.Standing := ⟨hn, hp, hc, hb⟩
  refine ⟨?_, ?_, card_FGreat_le I hI' eps h0 h1⟩
  · obtain ⟨π', hπ', -⟩ := (theorem_3 I hI' eps h0 h1).2 _ hpath0
    exact exists_optPath I eps _ ⟨π', hπ'⟩
  · intro π hπ
    obtain ⟨hTS, hEq⟩ := pathCost_eq_expectedCost I hI' eps h0 h1 _ hGF π hπ.1
    refine ⟨hTS, fun S hS => ?_⟩
    have hr1 := (rounding_sandwich I hI' eps h0 h1 _ hTS).1
    obtain ⟨π0, hπ0, hle0⟩ := greedy_within_class I hI' eps h0 h1 S hS
    have hr2 := (rounding_sandwich I hI' eps h0 h1 S hS).2
    obtain ⟨π', hπ', hle'⟩ := (theorem_3 I hI' eps h0 h1).2 π0 hπ0
    have hopt := hπ.2 π' hπ'
    unfold expectedCost
    calc expectedCostWith I I.c (schemeOf I eps π)
        ≤ expectedCostWith I (roundedCost I eps) (schemeOf I eps π) := hr1
      _ = cmin I * pathCost I eps π := hEq
      _ ≤ cmin I * pathCost I eps π' := mul_le_mul_of_nonneg_left hopt hcmin
      _ ≤ cmin I * (K eps * pathCost I eps π0) := mul_le_mul_of_nonneg_left hle' hcmin
      _ = K eps * (cmin I * pathCost I eps π0) := by ring
      _ ≤ K eps * expectedCostWith I (roundedCost I eps) S := mul_le_mul_of_nonneg_left hle0 hK
      _ ≤ K eps * ((1 + eps) * expectedCostWith I I.c S) := mul_le_mul_of_nonneg_left hr2 hK
      _ = (1 + eps) * K eps * expectedCostWith I I.c S := by ring
