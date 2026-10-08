-- Prove2me | solution 1 for CoresConvexGames.Stability.dominated_by_core_of_not_mem_core
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T19:10:54.855593+00:00
-- url     : https://prove2.me/submissions/f9fb5962-4716-4bf1-b8be-47bc5c4f3b2c

import Mathlib
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn
import Definitions.Def_Supermodularity_Cooperative_IsConvexGame
import Definitions.Def_Supermodularity_Cooperative_Core
import Definitions.Def_CoresConvexGames_Stability_IsFeasible
import Definitions.Def_CoresConvexGames_Stability_Dominates

set_option autoImplicit false

open scoped BigOperators

/-! External stability of the core of a convex game (Shapley 1971, proof of Theorem 8).
A feasible payoff vector outside the core has a blocking coalition of minimum size; adding the
uniform deficit share gives a payoff in the core of the subgame that strictly improves its members;
one-player marginal extensions (supermodularity) extend it to the whole core.
The overall plan follows an earlier, unaccepted attempt by `sometik179` (submission d13e8127), whose
inlined copies of the platform definitions caused its type mismatch; here the definitions are imported. -/

namespace ShapleyCoreProof

open Supermodularity.Cooperative CoresConvexGames.Stability

theorem extend_one {n : ℕ} (f : Finset (Fin n) → ℝ) (hf : IsConvexGame f)
    (S : Finset (Fin n)) (a : Fin n → ℝ) (ha : a ∈ Core S f)
    (j : Fin n) (hj : j ∉ S) :
    ∃ c ∈ Core (insert j S) f, ∀ i ∈ S, c i = a i := by
  classical
  let c := Function.update a j (f (insert j S) - f S)
  have hc : ∀ i ∈ S, c i = a i := by
    intro i hi
    exact Function.update_of_ne (ne_of_mem_of_not_mem hi hj) _ _
  have hsum : ∑ i ∈ S, c i = f S := by
    rw [Finset.sum_congr rfl hc]
    exact ha.1
  refine ⟨c, ⟨?_, ?_⟩, hc⟩
  · rw [Finset.sum_insert hj, hsum]
    simp [c]
  · intro T hT
    by_cases hjT : j ∈ T
    · have hTS : T.erase j ⊆ S := by
        intro i hi
        have hit := hT (Finset.mem_of_mem_erase hi)
        rcases Finset.mem_insert.mp hit with rfl | his
        · exact False.elim ((Finset.ne_of_mem_erase hi) rfl)
        · exact his
      have hTU : T ∪ S = insert j S := by
        ext i
        constructor
        · intro hi
          rcases Finset.mem_union.mp hi with hit | his
          · exact hT hit
          · exact Finset.mem_insert_of_mem his
        · intro hi
          rcases Finset.mem_insert.mp hi with rfl | his
          · exact Finset.mem_union_left S hjT
          · exact Finset.mem_union_right T his
      have hTI : T ∩ S = T.erase j := by
        ext i
        simp only [Finset.mem_inter, Finset.mem_erase]
        constructor
        · rintro ⟨hiT, hiS⟩
          exact ⟨ne_of_mem_of_not_mem hiS hj, hiT⟩
        · rintro ⟨hij, hiT⟩
          exact ⟨hiT, hTS (Finset.mem_erase.mpr ⟨hij, hiT⟩)⟩
      have hsm := hf.2 (x := T) (Set.mem_univ T) (y := S) (Set.mem_univ S)
      change f T + f S ≤ f (T ∪ S) + f (T ∩ S) at hsm
      rw [hTU, hTI] at hsm
      have hacc := ha.2 (T.erase j) hTS
      have hcsum : ∑ i ∈ T.erase j, c i = ∑ i ∈ T.erase j, a i :=
        Finset.sum_congr rfl (fun i hi => hc i (hTS hi))
      rw [← Finset.sum_erase_add _ _ hjT, hcsum]
      have hcj : c j = f (insert j S) - f S := by simp [c]
      rw [hcj]
      linarith
    · have hTS : T ⊆ S := by
        intro i hi
        rcases Finset.mem_insert.mp (hT hi) with rfl | his
        · exact False.elim (hjT hi)
        · exact his
      calc f T ≤ ∑ i ∈ T, a i := ha.2 T hTS
        _ = ∑ i ∈ T, c i := (Finset.sum_congr rfl (fun i hi => hc i (hTS hi))).symm

theorem core_extension {n : ℕ} (f : Finset (Fin n) → ℝ) (hf : IsConvexGame f)
    (S : Finset (Fin n)) (a : Fin n → ℝ) (ha : a ∈ Core S f) :
    ∃ c ∈ Core Finset.univ f, ∀ i ∈ S, c i = a i := by
  classical
  have aux (R : Finset (Fin n)) :
      ∃ c ∈ Core (S ∪ R) f, ∀ i ∈ S, c i = a i := by
    induction R using Finset.induction_on with
    | empty => simpa using ⟨a, ha, fun i (_ : i ∈ S) => rfl⟩
    | @insert j R hj ih =>
      obtain ⟨c, hc, heq⟩ := ih
      by_cases hjS : j ∈ S ∪ R
      · have hu : S ∪ insert j R = S ∪ R := by
          rw [Finset.union_insert, Finset.insert_eq_of_mem hjS]
        rw [hu]
        exact ⟨c, hc, heq⟩
      · obtain ⟨d, hd, hdc⟩ := extend_one f hf (S ∪ R) c hc j hjS
        rw [Finset.union_insert]
        refine ⟨d, hd, ?_⟩
        intro i hi
        exact (hdc i (Finset.mem_union_left R hi)).trans (heq i hi)
  obtain ⟨c, hc, heq⟩ := aux Finset.univ
  have hu : S ∪ Finset.univ = Finset.univ := by
    ext i
    simp
  exact ⟨c, hu ▸ hc, heq⟩

lemma exists_minimal_block {n : ℕ} (f : Finset (Fin n) → ℝ) (hf0 : f ∅ = 0)
    (b : Fin n → ℝ) (hb : IsFeasible f b) (hbc : b ∉ Core Finset.univ f) :
    ∃ S : Finset (Fin n), S.Nonempty ∧ (∑ i ∈ S, b i) < f S ∧
      ∀ T, T ⊂ S → f T ≤ ∑ i ∈ T, b i := by
  classical
  have hex : ∃ S : Finset (Fin n), (∑ i ∈ S, b i) < f S := by
    by_contra h
    push Not at h
    apply hbc
    refine ⟨le_antisymm hb (h Finset.univ), ?_⟩
    intro S _
    exact h S
  let blocks := (Finset.univ : Finset (Finset (Fin n))).filter
    (fun S => (∑ i ∈ S, b i) < f S)
  have hblocks : blocks.Nonempty := by
    obtain ⟨S, hS⟩ := hex
    exact ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS⟩⟩
  obtain ⟨S, hS, hmin⟩ := Finset.exists_min_image blocks Finset.card hblocks
  have hSb : (∑ i ∈ S, b i) < f S := (Finset.mem_filter.mp hS).2
  refine ⟨S, ?_, hSb, ?_⟩
  · by_contra hn
    have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp [he, hf0] at hSb
  · intro T hT
    by_contra ht
    have ht' : T ∈ blocks := Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_not_ge ht⟩
    exact (not_le_of_gt (Finset.card_lt_card hT)) (hmin T ht')

lemma blocking_subgame_core {n : ℕ} (f : Finset (Fin n) → ℝ)
    (b : Fin n → ℝ) (S : Finset (Fin n)) (hS : S.Nonempty)
    (hSb : (∑ i ∈ S, b i) < f S)
    (hmin : ∀ T, T ⊂ S → f T ≤ ∑ i ∈ T, b i) :
    ∃ a ∈ Core S f, ∀ i ∈ S, b i < a i := by
  classical
  let d : ℝ := (f S - ∑ i ∈ S, b i) / (S.card : ℝ)
  have hc : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hd : 0 < d := div_pos (sub_pos.mpr hSb) hc
  let a : Fin n → ℝ := fun i => b i + d
  have ha_sum : (∑ i ∈ S, a i) = f S := by
    simp only [a, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    dsimp [d]
    rw [mul_div_cancel₀ _ (ne_of_gt hc)]
    linarith
  refine ⟨a, ⟨ha_sum, ?_⟩, ?_⟩
  · intro T hT
    by_cases heq : T = S
    · simpa [heq] using ha_sum.ge
    · have hproper : T ⊂ S := Finset.ssubset_iff_subset_ne.mpr ⟨hT, heq⟩
      exact (hmin T hproper).trans (Finset.sum_le_sum (fun i _ => by
        dsimp [a]
        linarith))
  · intro i _
    dsimp [a]
    linarith

end ShapleyCoreProof

open Supermodularity.Cooperative CoresConvexGames.Stability ShapleyCoreProof in
theorem solution {n : ℕ} (f : Finset (Fin n) → ℝ) (hf : IsConvexGame f) (b : Fin n → ℝ)
    (hb : IsFeasible f b) (hbC : b ∉ Core Finset.univ f) :
    ∃ a ∈ Core Finset.univ f, Dominates f a b := by
  obtain ⟨S, hS, hSb, hmin⟩ := exists_minimal_block f hf.1 b hb hbC
  obtain ⟨a, ha, hab⟩ := blocking_subgame_core f b S hS hSb hmin
  obtain ⟨c, hc, hca⟩ := core_extension f hf S a ha
  refine ⟨c, hc, S, hS, ?_, ?_⟩
  · exact (Finset.sum_congr rfl hca).trans ha.1 |>.le
  · intro i hi
    rw [hca i hi]
    exact hab i hi
