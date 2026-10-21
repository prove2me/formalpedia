-- Prove2me | solution 1 for ConsHalving.Additive.theorem_2_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T15:02:52.506445+00:00
-- url     : https://prove2.me/submissions/1ec00431-ba03-446f-b7f7-4189102c5e14

import Mathlib
import Definitions.Def_ConsHalving_Additive_Setting
import Theorems.Thm_ConsHalving_Additive_half_case
import Theorems.Thm_ConsHalving_Additive_termination_card
import Theorems.Thm_ConsHalving_Additive_step_3_invariant

open ConsHalving.Additive

/-- Items in `U` that are wholly in one part are not cut, so the cut items and `U` are disjoint. -/
private lemma cuts_add_le {m : ℕ} (z : Fin m → ℝ) (U : Finset (Fin m))
    (hU : ∀ j ∈ U, z j = 0 ∨ z j = 1) : numCuts z + U.card ≤ m := by
  classical
  unfold numCuts
  have hdisj : Disjoint (Finset.univ.filter (fun j => IsCut z j)) U := by
    rw [Finset.disjoint_left]
    intro j hj hjU
    have hc := (Finset.mem_filter.1 hj).2
    unfold IsCut at hc
    rcases hU j hjU with h | h <;> rw [h] at hc <;> norm_num at hc
  have := Finset.card_union_of_disjoint hdisj
  have hle := Finset.card_le_univ (Finset.univ.filter (fun j => IsCut z j) ∪ U)
  simp only [Fintype.card_fin] at hle
  convert (this ▸ hle) using 3

/-- For a fractional `z`, every item is either cut or wholly in one part. -/
private lemma cuts_add_ge {m : ℕ} (z : Fin m → ℝ) (hz : IsFractional z) :
    m ≤ numCuts z + (Finset.univ.filter (fun j => z j = 0 ∨ z j = 1)).card := by
  classical
  unfold numCuts
  have hsub : (Finset.univ : Finset (Fin m)) ⊆
      Finset.univ.filter (fun j => IsCut z j) ∪
        Finset.univ.filter (fun j => z j = 0 ∨ z j = 1) := by
    intro j _
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    by_cases h0 : z j = 0
    · exact Or.inr ⟨Finset.mem_univ _, Or.inl h0⟩
    by_cases h1 : z j = 1
    · exact Or.inr ⟨Finset.mem_univ _, Or.inr h1⟩
    left
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · exact lt_of_le_of_ne (hz j).1 (Ne.symm h0)
    · have := lt_of_le_of_ne (hz j).2 h1
      linarith
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le (Finset.univ.filter (fun j => IsCut z j))
    (Finset.univ.filter (fun j => z j = 0 ∨ z j = 1))
  simp only [Finset.card_univ, Fintype.card_fin] at h1
  have := le_trans h1 h2
  convert this using 2

theorem solution {n m : ℕ} (u : Fin n → Fin m → ℝ) (hu : ∀ i j, 0 ≤ u i j) :
    ∃ x : Fin m → ℝ, IsConsensusHalving u x ∧ numCuts x ≤ min n m := by
  classical
  by_cases hmn : m ≤ n
  · obtain ⟨h1, h2⟩ := half_case u hmn
    exact ⟨_, h1, h2.le⟩
  push_neg at hmn
  rw [min_eq_left hmn.le]
  -- splitting every item in half is a consensus halving
  have hhalf : IsConsensusHalving u (fun _ => 1 / 2) := by
    refine ⟨fun j => by norm_num, fun i => ?_⟩
    unfold util
    exact Finset.sum_congr rfl fun j _ => by norm_num
  -- take a consensus halving with the fewest cuts
  have hP : ∃ k, ∃ x, IsConsensusHalving u x ∧ numCuts x = k := ⟨_, _, hhalf, rfl⟩
  obtain ⟨x, hx, hxk⟩ := Nat.find_spec hP
  have hxmin : ∀ z, IsConsensusHalving u z → numCuts x ≤ numCuts z := by
    intro z hz
    rw [hxk]
    exact Nat.find_min' hP ⟨z, hz, rfl⟩
  refine ⟨x, hx, ?_⟩
  by_contra hgt
  push_neg at hgt
  set T := Finset.univ.filter (fun j => x j = 0 ∨ x j = 1) with hTdef
  have hTx : ∀ j ∈ T, x j = 0 ∨ x j = 1 := fun j hj => (Finset.mem_filter.1 hj).2
  have hle := cuts_add_le x T hTx
  have hge : m ≤ numCuts x + T.card := by
    convert cuts_add_ge x hx.1
  -- `x` solves the system `S`
  have hxS : SolvesS u x := by
    intro i
    have h := hx.2 i
    unfold util at h
    have : ∑ j, (x j - 1 / 2) * u i j =
        (1 / 2) * (∑ j, x j * u i j - ∑ j, (1 - x j) * u i j) := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [this, h, sub_self, mul_zero]
  -- `x` is not the unique solution of `S ∪ T`, since `|T| < m - n`
  have hnotuniq : ¬ ∀ y, SolvesST u T x y → y = x := by
    intro huniq
    have := termination_card u T x hxS huniq
    omega
  push_neg at hnotuniq
  obtain ⟨y, hy, hyx⟩ := hnotuniq
  obtain ⟨j0, hj0⟩ := Function.ne_iff.1 hyx
  have hD : (Finset.univ.filter (fun j => y j ≠ x j)).Nonempty :=
    ⟨j0, Finset.mem_filter.2 ⟨Finset.mem_univ _, hj0⟩⟩
  obtain ⟨jstar, hjD, hjmin⟩ := Finset.exists_min_image _ (gamma x y) hD
  have hstar : y jstar ≠ x jstar := (Finset.mem_filter.1 hjD).2
  have hmin : ∀ j, y j ≠ x j → gamma x y jstar ≤ gamma x y j :=
    fun j hj => hjmin j (Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩)
  obtain ⟨hs, hnotT, hU⟩ := step_3_invariant u T x y jstar hx hTx hy hstar hmin
  have hsle := cuts_add_le _ _ hU
  rw [Finset.card_insert_of_notMem hnotT] at hsle
  have := hxmin _ hs
  omega
