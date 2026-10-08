-- Prove2me | solution 1 for CompetitivePaging.Combining.realizable_iff
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-04T23:25:08.205032+00:00
-- url     : https://prove2.me/submissions/aa128f4d-a493-44b9-94b0-e49e0bb1fe37

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_CompetitivePaging_Combining_Realizable

set_option autoImplicit false


/- Inlined checked module: DeadlineScheduler -/
section
set_option autoImplicit false

namespace CompetitivePaging.Combining

/-- Every completed deadline precedes every next deadline. -/
def DeadlineBalanced {m : ℕ} (c : Fin m → ℝ) (N : Fin m → ℕ) : Prop :=
  ∀ i j, c i * (N i : ℝ) ≤ c j * ((N j : ℝ) + 1)

theorem deadlineBalanced_zero {m : ℕ} (c : Fin m → ℝ) (hc : ∀ i, 0 < c i) :
    DeadlineBalanced c (fun _ => 0) := by
  intro i j
  simpa using (hc j).le

theorem exists_next_deadline {m : ℕ} (hm : 0 < m) (c : Fin m → ℝ)
    (N : Fin m → ℕ) :
    ∃ i, ∀ j, c i * ((N i : ℝ) + 1) ≤ c j * ((N j : ℝ) + 1) := by
  have hne : (Finset.univ : Finset (Fin m)).Nonempty := ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  obtain ⟨i, _, hi⟩ := Finset.exists_min_image Finset.univ
    (fun j => c j * ((N j : ℝ) + 1)) hne
  exact ⟨i, fun j => hi j (Finset.mem_univ _)⟩

theorem DeadlineBalanced.increment {m : ℕ} {c : Fin m → ℝ} {N : Fin m → ℕ}
    (hc : ∀ i, 0 < c i) (hN : DeadlineBalanced c N) (i : Fin m)
    (hi : ∀ j, c i * ((N i : ℝ) + 1) ≤ c j * ((N j : ℝ) + 1)) :
    DeadlineBalanced c (Function.update N i (N i + 1)) := by
  intro j k
  by_cases hj : j = i
  · subst j
    by_cases hk : k = i
    · subst k
      simp only [Function.update_self, Nat.cast_add, Nat.cast_one]
      nlinarith [hc i]
    · simpa only [Function.update_self, Function.update_of_ne hk,
        Nat.cast_add, Nat.cast_one] using hi k
  · by_cases hk : k = i
    · subst k
      simp only [Function.update_of_ne hj, Function.update_self, Nat.cast_add, Nat.cast_one]
      have h := hN j i
      nlinarith [hc i]
    · simpa only [Function.update_of_ne hj, Function.update_of_ne hk] using hN j k

/-- Exact load bound, including the boundary where the reciprocal ratios sum to one. -/
theorem DeadlineBalanced.total_le {m : ℕ} {c : Fin m → ℝ} {N : Fin m → ℕ}
    (hc : ∀ i, 0 < c i) (hs : ∑ j, 1 / c j ≤ 1)
    (hN : DeadlineBalanced c N) (i : Fin m) :
    (∑ j, (N j : ℝ)) ≤ c i * ((N i : ℝ) + 1) := by
  let L := c i * ((N i : ℝ) + 1)
  have hL : 0 ≤ L := mul_nonneg (hc i).le (by positivity)
  calc
    (∑ j, (N j : ℝ)) ≤ ∑ j, L / c j :=
      Finset.sum_le_sum (fun j _ => (le_div_iff₀ (hc j)).2 (by
        simpa only [mul_comm] using hN j i))
    _ = L * (∑ j, 1 / c j) := by simp [Finset.mul_sum, div_eq_mul_inv]
    _ ≤ L * 1 := mul_le_mul_of_nonneg_left hs hL
    _ = c i * ((N i : ℝ) + 1) := by simp [L]

end CompetitivePaging.Combining
end


/- Inlined checked module: OccupancyPotential -/
section
set_option autoImplicit false

namespace CompetitivePaging.Combining

open Finset

noncomputable def occupied {k : ℕ} {M : Type*} (C : KServer.Config k M) : Finset M := by
  classical
  exact Finset.univ.image C

theorem mem_occupied {k : ℕ} {M : Type*} (C : KServer.Config k M) (x : M) :
    x ∈ occupied C ↔ ∃ j, C j = x := by
  classical
  simp [occupied]

theorem occupied_card_le {k : ℕ} {M : Type*} (C : KServer.Config k M) :
    (occupied C).card ≤ k := by
  classical
  exact (Finset.card_image_le).trans_eq (Fintype.card_fin k)

theorem occupied_card {k : ℕ} {M : Type*} {C : KServer.Config k M}
    (hC : Function.Injective C) : (occupied C).card = k := by
  classical
  simp only [occupied, Finset.card_image_of_injective _ hC, Finset.card_univ,
    Fintype.card_fin]

noncomputable def missing {k : ℕ} {M : Type*}
    (C D : KServer.Config k M) : ℕ := by
  classical
  exact (occupied C \ occupied D).card

theorem missing_le {k : ℕ} {M : Type*} (C D : KServer.Config k M) : missing C D ≤ k := by
  classical
  exact (Finset.card_le_card Finset.sdiff_subset).trans (occupied_card_le C)

theorem card_sdiff_triangle {M : Type*} [DecidableEq M] (A B D : Finset M) :
    (A \ D).card ≤ (A \ B).card + (B \ D).card := by
  have h : A \ D ⊆ (A \ B) ∪ (B \ D) := by
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_union] at *
    by_cases hB : x ∈ B
    · exact Or.inr ⟨hB, hx.2⟩
    · exact Or.inl ⟨hx.1, hB⟩
  exact (Finset.card_le_card h).trans (Finset.card_union_le _ _)

/-- Every page lost by a comparator has at least one label that moved. -/
theorem lost_occupied_le_moves {k : ℕ} {M : Type*} [MetricSpace M] [DecidableEq M]
    (huniform : ∀ x y : M, x ≠ y → dist x y = 1)
    (D E : KServer.Config k M) :
    ((occupied D \ occupied E).card : ℝ) ≤ KServer.moveCost D E := by
  classical
  let S := Finset.univ.filter (fun j => D j ≠ E j)
  have hsub : occupied D \ occupied E ⊆ S.image D := by
    intro x hx
    obtain ⟨hxD, hxE⟩ := Finset.mem_sdiff.mp hx
    obtain ⟨j, hj⟩ := (mem_occupied D x).mp hxD
    refine Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hj⟩
    intro heq
    exact hxE ((mem_occupied E x).mpr ⟨j, heq.symm.trans hj⟩)
  have hcard : (occupied D \ occupied E).card ≤ S.card :=
    (Finset.card_le_card hsub).trans Finset.card_image_le
  have hcost : KServer.moveCost D E = (S.card : ℝ) := by
    unfold KServer.moveCost
    rw [← Finset.sum_boole]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : D j = E j
    · simp [h]
    · simp [h, huniform _ _ h]
  rw [hcost]
  exact_mod_cast hcard

/-- Arbitrary simultaneous comparator moves increase the occupancy potential by at most cost. -/
theorem missing_comparator_step {k : ℕ} {M : Type*} [MetricSpace M]
    (huniform : ∀ x y : M, x ≠ y → dist x y = 1)
    (C D E : KServer.Config k M) :
    (missing C E : ℝ) ≤ (missing C D : ℝ) + KServer.moveCost D E := by
  classical
  have h := card_sdiff_triangle (occupied C) (occupied D) (occupied E)
  have h' : (missing C E : ℝ) ≤ (missing C D : ℝ) + ((occupied D \ occupied E).card : ℝ) := by
    exact_mod_cast h
  exact h'.trans (add_le_add le_rfl (lost_occupied_le_moves huniform D E))

end CompetitivePaging.Combining
end


/- Inlined checked module: LazyEviction -/
section
set_option autoImplicit false

namespace CompetitivePaging.Combining

open Finset

/-- A full injective cache can evict a page missing from any updated comparator. -/
theorem exists_eviction {k : ℕ} {M : Type*} {C : KServer.Config k M}
    (hC : Function.Injective C) (D : KServer.Config k M) (r : M)
    (hrC : r ∉ occupied C) (hrD : r ∈ occupied D) :
    ∃ j, C j ∉ occupied D := by
  classical
  by_contra h
  have hsub : occupied C ⊆ occupied D := by
    intro x hx
    obtain ⟨j, rfl⟩ := (mem_occupied C x).mp hx
    by_contra hj
    exact h ⟨j, hj⟩
  have hi : insert r (occupied C) ⊆ occupied D := insert_subset hrD hsub
  have hcard := (card_le_card hi).trans (occupied_card_le D)
  rw [card_insert_of_notMem hrC, occupied_card hC] at hcard
  omega

theorem update_injective_fresh {k : ℕ} {M : Type*} {C : KServer.Config k M}
    (hC : Function.Injective C) (j : Fin k) (r : M) (hr : r ∉ occupied C) :
    Function.Injective (Function.update C j r) := by
  intro a b hab
  by_cases ha : a = j
  · subst a
    by_cases hb : b = j
    · exact hb.symm
    · simp only [Function.update_self, Function.update_of_ne hb] at hab
      exact False.elim (hr ((mem_occupied C r).mpr ⟨b, hab.symm⟩))
  · by_cases hb : b = j
    · subst b
      simp only [Function.update_self, Function.update_of_ne ha] at hab
      exact False.elim (hr ((mem_occupied C r).mpr ⟨a, hab⟩))
    · exact hC (by simpa only [Function.update_of_ne ha, Function.update_of_ne hb] using hab)

theorem occupied_update {k : ℕ} {M : Type*} [DecidableEq M] {C : KServer.Config k M}
    (hC : Function.Injective C) (j : Fin k) (r : M) :
    occupied (Function.update C j r) = insert r ((occupied C).erase (C j)) := by
  ext x
  rw [mem_occupied, mem_insert, mem_erase, mem_occupied]
  constructor
  · rintro ⟨a, ha⟩
    by_cases haj : a = j
    · subst a
      exact Or.inl (by simpa only [Function.update_self] using ha.symm)
    · right
      have hax : C a = x := by simpa only [Function.update_of_ne haj] using ha
      exact ⟨fun hx => haj (hC (hax.trans hx)), ⟨a, hax⟩⟩
  · rintro (rfl | ⟨hne, a, ha⟩)
    · exact ⟨j, Function.update_self _ _ _⟩
    · have haj : a ≠ j := fun h => hne (ha.symm.trans (congrArg C h))
      exact ⟨a, by simpa only [Function.update_of_ne haj] using ha⟩

theorem missing_update_le {k : ℕ} {M : Type*} {C : KServer.Config k M}
    (hC : Function.Injective C) (D : KServer.Config k M) (j : Fin k) (r : M)
    (hrD : r ∈ occupied D) : missing (Function.update C j r) D ≤ missing C D := by
  classical
  unfold missing
  rw [occupied_update hC]
  apply card_le_card
  intro x hx
  simp only [mem_sdiff, mem_insert, mem_erase] at hx ⊢
  rcases hx.1 with hxr | hxC
  · exact False.elim (hx.2 (hxr ▸ hrD))
  · exact ⟨hxC.2, hx.2⟩

/-- The chosen comparator pays exactly one unit of occupancy potential. -/
theorem missing_update_add_one {k : ℕ} {M : Type*} {C : KServer.Config k M}
    (hC : Function.Injective C) (D : KServer.Config k M) (j : Fin k) (r : M)
    (hrD : r ∈ occupied D) (hjD : C j ∉ occupied D) :
    missing (Function.update C j r) D + 1 = missing C D := by
  classical
  have hset : insert r ((occupied C).erase (C j)) \ occupied D =
      (occupied C \ occupied D).erase (C j) := by
    ext x
    simp only [mem_sdiff, mem_insert, mem_erase]
    constructor
    · rintro ⟨hxr | hxC, hxD⟩
      · exact False.elim (hxD (hxr ▸ hrD))
      · exact ⟨hxC.1, hxC.2, hxD⟩
    · rintro ⟨hne, hxC, hxD⟩
      exact ⟨Or.inr ⟨hne, hxC⟩, hxD⟩
  unfold missing
  rw [occupied_update hC, hset]
  exact card_erase_add_one (mem_sdiff.mpr ⟨(mem_occupied C (C j)).mpr ⟨j, rfl⟩, hjD⟩)

end CompetitivePaging.Combining
end


/- Inlined checked module: OnlineCost -/
section
set_option autoImplicit false

namespace CompetitivePaging.Combining

theorem moveCost_nonneg {k : ℕ} {M : Type*} [MetricSpace M]
    (C D : KServer.Config k M) : 0 ≤ KServer.moveCost C D :=
  Finset.sum_nonneg (fun _ _ => dist_nonneg)

theorem moveCost_self {k : ℕ} {M : Type*} [MetricSpace M]
    (C : KServer.Config k M) : KServer.moveCost C C = 0 := by
  simp [KServer.moveCost]

theorem cost_nonneg {k : ℕ} {M : Type*} [MetricSpace M]
    (A : KServer.OnlineAlgorithm k M) (l : List M) : 0 ≤ A.cost l :=
  Finset.sum_nonneg (fun _ _ => moveCost_nonneg _ _)

theorem cost_nil {k : ℕ} {M : Type*} [MetricSpace M]
    (A : KServer.OnlineAlgorithm k M) : A.cost [] = 0 := by
  simp [KServer.OnlineAlgorithm.cost]

theorem cost_append {k : ℕ} {M : Type*} [MetricSpace M]
    (A : KServer.OnlineAlgorithm k M) (l : List M) (r : M) :
    A.cost (l ++ [r]) = A.cost l + KServer.moveCost (A.conf l) (A.conf (l ++ [r])) := by
  unfold KServer.OnlineAlgorithm.cost
  simp only [List.length_append, List.length_singleton, Finset.sum_range_succ,
    List.take_length_add_append]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [List.take_append_of_le_length (Nat.le_of_lt hj'),
      List.take_append_of_le_length (Nat.succ_le_of_lt hj')]
  · simp [List.take_append_of_le_length (le_refl l.length)]

theorem moveCost_update {k : ℕ} {M : Type*} [MetricSpace M]
    (C : KServer.Config k M) (j : Fin k) (r : M) :
    KServer.moveCost C (Function.update C j r) = dist (C j) r := by
  unfold KServer.moveCost
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [Function.update_of_ne hij]
  · intro hj
    exact False.elim (hj (Finset.mem_univ j))

theorem sum_increment {m : ℕ} (N : Fin m → ℕ) (i : Fin m) :
    (∑ j, (Function.update N i (N i + 1) j : ℝ)) = (∑ j, (N j : ℝ)) + 1 := by
  have h : (fun j => (Function.update N i (N i + 1) j : ℝ)) =
      fun j => (N j : ℝ) + if j = i then 1 else 0 := by
    funext j
    by_cases hj : j = i
    · subst j
      simp
    · simp [hj]
  rw [h, Finset.sum_add_distrib]
  simp

end CompetitivePaging.Combining
end


/- Inlined checked module: CombinedStep -/
section
set_option autoImplicit false

namespace CompetitivePaging.Combining

structure CacheState (k m : ℕ) (M : Type*) where
  conf : KServer.Config k M
  injective : Function.Injective conf
  assigned : Fin m → ℕ

noncomputable def nextExpert {m : ℕ} (hm : 0 < m) (c : Fin m → ℝ)
    (N : Fin m → ℕ) : Fin m := (exists_next_deadline hm c N).choose

theorem nextExpert_min {m : ℕ} (hm : 0 < m) (c : Fin m → ℝ) (N : Fin m → ℕ) :
    ∀ j, c (nextExpert hm c N) * ((N (nextExpert hm c N) : ℝ) + 1) ≤
      c j * ((N j : ℝ) + 1) := (exists_next_deadline hm c N).choose_spec

noncomputable def bump {k m : ℕ} {M : Type*} (s : CacheState k m M)
    (i : Fin m) (j : Fin k) (r : M) (hr : r ∉ occupied s.conf) : CacheState k m M where
  conf := Function.update s.conf j r
  injective := update_injective_fresh s.injective j r hr
  assigned := Function.update s.assigned i (s.assigned i + 1)

noncomputable def combinedStep {k m : ℕ} {M : Type*} [MetricSpace M]
    (hm : 0 < m) (c : Fin m → ℝ) (B : Fin m → KServer.OnlineAlgorithm k M)
    (l : List M) (r : M) (s : CacheState k m M) : CacheState k m M := by
  classical
  exact if hr : r ∈ occupied s.conf then s else
    let i := nextExpert hm c s.assigned
    let hj := exists_eviction s.injective ((B i).conf (l ++ [r])) r hr
      ((mem_occupied _ _).mpr ((B i).serves l r))
    bump s i hj.choose r hr

theorem combinedStep_serves {k m : ℕ} {M : Type*} [MetricSpace M]
    (hm : 0 < m) (c : Fin m → ℝ) (B : Fin m → KServer.OnlineAlgorithm k M)
    (l : List M) (r : M) (s : CacheState k m M) :
    ∃ j, (combinedStep hm c B l r s).conf j = r := by
  classical
  unfold combinedStep
  split_ifs with hr
  · exact (mem_occupied _ _).mp hr
  · dsimp
    exact ⟨_, Function.update_self _ _ _⟩

theorem combinedStep_balanced {k m : ℕ} {M : Type*} [MetricSpace M]
    (hm : 0 < m) (c : Fin m → ℝ) (hc : ∀ i, 0 < c i)
    (B : Fin m → KServer.OnlineAlgorithm k M)
    (l : List M) (r : M) (s : CacheState k m M)
    (hs : DeadlineBalanced c s.assigned) :
    DeadlineBalanced c (combinedStep hm c B l r s).assigned := by
  classical
  unfold combinedStep
  split_ifs
  · exact hs
  · exact hs.increment hc (nextExpert hm c s.assigned) (nextExpert_min hm c s.assigned)

theorem combinedStep_cost {k m : ℕ} {M : Type*} [MetricSpace M]
    (huniform : ∀ x y : M, x ≠ y → dist x y = 1)
    (hm : 0 < m) (c : Fin m → ℝ) (B : Fin m → KServer.OnlineAlgorithm k M)
    (l : List M) (r : M) (s : CacheState k m M) :
    (∑ i, ((combinedStep hm c B l r s).assigned i : ℝ)) =
      (∑ i, (s.assigned i : ℝ)) +
        KServer.moveCost s.conf (combinedStep hm c B l r s).conf := by
  classical
  unfold combinedStep
  split_ifs with hr
  · rw [moveCost_self, add_zero]
  · dsimp [bump]
    rw [sum_increment, moveCost_update]
    congr 1
    symm
    apply huniform
    intro h
    exact hr ((mem_occupied _ _).mpr ⟨_, h⟩)

/-- One step charges its assigned comparator through a decreasing potential. -/
theorem combinedStep_charge {k m : ℕ} {M : Type*} [MetricSpace M]
    (hm : 0 < m) (c : Fin m → ℝ) (B : Fin m → KServer.OnlineAlgorithm k M)
    (l : List M) (r : M) (s : CacheState k m M) (i : Fin m) :
    ((combinedStep hm c B l r s).assigned i : ℝ) +
        (missing (combinedStep hm c B l r s).conf ((B i).conf (l ++ [r])) : ℝ) ≤
      (s.assigned i : ℝ) + (missing s.conf ((B i).conf (l ++ [r])) : ℝ) := by
  classical
  unfold combinedStep
  split_ifs with hr
  · exact le_rfl
  · let a := nextExpert hm c s.assigned
    let hj := exists_eviction s.injective ((B a).conf (l ++ [r])) r hr
      ((mem_occupied _ _).mpr ((B a).serves l r))
    change (Function.update s.assigned a (s.assigned a + 1) i : ℝ) +
      (missing (Function.update s.conf hj.choose r) ((B i).conf (l ++ [r])) : ℝ) ≤ _
    have hri : r ∈ occupied ((B i).conf (l ++ [r])) :=
      (mem_occupied _ _).mpr ((B i).serves l r)
    by_cases hi : i = a
    · subst i
      rw [Function.update_self, Nat.cast_add, Nat.cast_one]
      have h := missing_update_add_one s.injective ((B a).conf (l ++ [r]))
        hj.choose r hri hj.choose_spec
      have h' : (missing (Function.update s.conf hj.choose r) ((B a).conf (l ++ [r])) : ℝ) + 1 =
          (missing s.conf ((B a).conf (l ++ [r])) : ℝ) := by exact_mod_cast h
      linarith
    · rw [Function.update_of_ne hi]
      have h := missing_update_le s.injective ((B i).conf (l ++ [r])) hj.choose r hri
      have h' : (missing (Function.update s.conf hj.choose r) ((B i).conf (l ++ [r])) : ℝ) ≤
          (missing s.conf ((B i).conf (l ++ [r])) : ℝ) := by exact_mod_cast h
      linarith

end CompetitivePaging.Combining
end


/- Inlined checked module: CombinedRun -/
section
set_option autoImplicit false

namespace CompetitivePaging.Combining

noncomputable def runCache {k m : ℕ} {M : Type*} [MetricSpace M]
    (hm : 0 < m) (c : Fin m → ℝ) (B : Fin m → KServer.OnlineAlgorithm k M)
    (C₀ : KServer.Config k M) (hC₀ : Function.Injective C₀) (l : List M) : CacheState k m M :=
  l.reverseRecOn ⟨C₀, hC₀, fun _ => 0⟩ (fun l r s => combinedStep hm c B l r s)

theorem runCache_nil {k m : ℕ} {M : Type*} [MetricSpace M]
    (hm : 0 < m) (c : Fin m → ℝ) (B : Fin m → KServer.OnlineAlgorithm k M)
    (C₀ : KServer.Config k M) (hC₀ : Function.Injective C₀) :
    runCache hm c B C₀ hC₀ [] = ⟨C₀, hC₀, fun _ => 0⟩ := by
  simp [runCache]

theorem runCache_append {k m : ℕ} {M : Type*} [MetricSpace M]
    (hm : 0 < m) (c : Fin m → ℝ) (B : Fin m → KServer.OnlineAlgorithm k M)
    (C₀ : KServer.Config k M) (hC₀ : Function.Injective C₀) (l : List M) (r : M) :
    runCache hm c B C₀ hC₀ (l ++ [r]) = combinedStep hm c B l r (runCache hm c B C₀ hC₀ l) := by
  simp [runCache]

noncomputable def combinedAlgorithm {k m : ℕ} {M : Type*} [MetricSpace M]
    (hm : 0 < m) (c : Fin m → ℝ) (B : Fin m → KServer.OnlineAlgorithm k M)
    (C₀ : KServer.Config k M) (hC₀ : Function.Injective C₀) : KServer.OnlineAlgorithm k M where
  conf l := (runCache hm c B C₀ hC₀ l).conf
  serves l r := by
    rw [runCache_append]
    exact combinedStep_serves hm c B l r _

theorem runCache_balanced {k m : ℕ} {M : Type*} [MetricSpace M]
    (hm : 0 < m) (c : Fin m → ℝ) (hc : ∀ i, 0 < c i)
    (B : Fin m → KServer.OnlineAlgorithm k M)
    (C₀ : KServer.Config k M) (hC₀ : Function.Injective C₀) (l : List M) :
    DeadlineBalanced c (runCache hm c B C₀ hC₀ l).assigned := by
  induction l using List.reverseRecOn with
  | nil => rw [runCache_nil]; exact deadlineBalanced_zero c hc
  | append_singleton l r ih =>
    rw [runCache_append]
    exact combinedStep_balanced hm c hc B l r _ ih

theorem runCache_charge {k m : ℕ} {M : Type*} [MetricSpace M]
    (huniform : ∀ x y : M, x ≠ y → dist x y = 1)
    (hm : 0 < m) (c : Fin m → ℝ) (B : Fin m → KServer.OnlineAlgorithm k M)
    (C₀ : KServer.Config k M) (hC₀ : Function.Injective C₀) (l : List M) (i : Fin m) :
    ((runCache hm c B C₀ hC₀ l).assigned i : ℝ) +
        (missing (runCache hm c B C₀ hC₀ l).conf ((B i).conf l) : ℝ) ≤
      (k : ℝ) + (B i).cost l := by
  induction l using List.reverseRecOn with
  | nil =>
    rw [runCache_nil, cost_nil]
    simpa using (Nat.cast_le.mpr (missing_le C₀ ((B i).conf [])) :
      (missing C₀ ((B i).conf []) : ℝ) ≤ (k : ℝ))
  | append_singleton l r ih =>
    rw [runCache_append, cost_append]
    have hstep := combinedStep_charge hm c B l r (runCache hm c B C₀ hC₀ l) i
    have hcomp := missing_comparator_step huniform (runCache hm c B C₀ hC₀ l).conf
      ((B i).conf l) ((B i).conf (l ++ [r]))
    linarith

theorem combinedAlgorithm_cost {k m : ℕ} {M : Type*} [MetricSpace M]
    (huniform : ∀ x y : M, x ≠ y → dist x y = 1)
    (hm : 0 < m) (c : Fin m → ℝ) (B : Fin m → KServer.OnlineAlgorithm k M)
    (C₀ : KServer.Config k M) (hC₀ : Function.Injective C₀) (l : List M) :
    (combinedAlgorithm hm c B C₀ hC₀).cost l = ∑ i, ((runCache hm c B C₀ hC₀ l).assigned i : ℝ) := by
  induction l using List.reverseRecOn with
  | nil => simp [cost_nil, runCache_nil]
  | append_singleton l r ih =>
    rw [cost_append, ih, runCache_append]
    have h := combinedStep_cost huniform hm c B l r (runCache hm c B C₀ hC₀ l)
    simpa only [combinedAlgorithm, runCache_append] using h.symm

theorem combinedAlgorithm_competitive {k m : ℕ} {M : Type} [MetricSpace M]
    (huniform : ∀ x y : M, x ≠ y → dist x y = 1)
    (hm : 0 < m) (c : Fin m → ℝ) (hc : ∀ i, 0 < c i) (hs : ∑ i, 1 / c i ≤ 1)
    (B : Fin m → KServer.OnlineAlgorithm k M)
    (C₀ : KServer.Config k M) (hC₀ : Function.Injective C₀) (i : Fin m) :
    CompetitiveAgainst (combinedAlgorithm hm c B C₀ hC₀) (B i) (c i) := by
  refine ⟨c i * ((k : ℝ) + 1), ?_⟩
  intro l
  have hbound := (runCache_balanced hm c hc B C₀ hC₀ l).total_le hc hs i
  have hcharge := runCache_charge huniform hm c B C₀ hC₀ l i
  have hcount : ((runCache hm c B C₀ hC₀ l).assigned i : ℝ) ≤ (k : ℝ) + (B i).cost l := by
    have hnonneg : (0 : ℝ) ≤ (missing (runCache hm c B C₀ hC₀ l).conf ((B i).conf l) : ℝ) := by positivity
    linarith
  rw [combinedAlgorithm_cost huniform]
  calc
    (∑ j, ((runCache hm c B C₀ hC₀ l).assigned j : ℝ)) ≤
        c i * (((runCache hm c B C₀ hC₀ l).assigned i : ℝ) + 1) := hbound
    _ ≤ c i * ((k : ℝ) + (B i).cost l + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (hc i).le
    _ = c i * (B i).cost l + c i * ((k : ℝ) + 1) := by ring

end CompetitivePaging.Combining
end


/- Inlined checked module: RealizableSufficiency -/
section
set_option autoImplicit false

namespace CompetitivePaging.Combining

theorem realizable_of_reciprocal_sum_le {m : ℕ} (hm : 0 < m)
    (c : Fin m → ℝ) (hc : ∀ i, 0 < c i) (hs : ∑ i, 1 / c i ≤ 1) :
    Realizable c := by
  classical
  intro k M _ _ huniform B
  by_cases hk : k ≤ Fintype.card M
  · obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
      (show Fintype.card (Fin k) ≤ Fintype.card M by simpa using hk)
    exact ⟨combinedAlgorithm hm c B e e.injective,
      fun i => combinedAlgorithm_competitive huniform hm c hc hs B e e.injective i⟩
  · obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
      (show Fintype.card M ≤ Fintype.card (Fin k) by simp; omega)
    let C : KServer.Config k M := Function.extend e id ((B ⟨0, hm⟩).conf [])
    have hC : ∀ r, ∃ j, C j = r := fun r => ⟨e r, e.injective.extend_apply id _ r⟩
    let A : KServer.OnlineAlgorithm k M := ⟨fun _ => C, fun _ r => hC r⟩
    refine ⟨A, fun i => ⟨0, fun l => ?_⟩⟩
    have hzero : A.cost l = 0 := by simp [KServer.OnlineAlgorithm.cost, A, KServer.moveCost]
    rw [hzero, add_zero]
    exact mul_nonneg (hc i).le (cost_nonneg (B i) l)

end CompetitivePaging.Combining
end


/- Inlined checked module: UniformMetric -/
section
set_option autoImplicit false

namespace CompetitivePaging.Combining

@[instance_reducible]
def uniformMetric (M : Type*) [DecidableEq M] : MetricSpace M where
  dist x y := if x = y then 0 else 1
  dist_self x := by simp
  dist_comm x y := by simp [eq_comm]
  dist_triangle x y z := by
    by_cases hxy : x = y
    · subst y; simp
    · by_cases hyz : y = z
      · subst z; simp
      · rw [if_neg hxy, if_neg hyz]
        split_ifs <;> norm_num
  eq_of_dist_eq_zero := by
    intro x y h
    by_contra hne
    simp [hne] at h

theorem uniformMetric_dist (M : Type*) [DecidableEq M] (x y : M) :
    @dist M (uniformMetric M).toDist x y = if x = y then 0 else 1 := rfl

theorem uniformMetric_dist_of_ne (M : Type*) [DecidableEq M] (x y : M) (h : x ≠ y) :
    @dist M (uniformMetric M).toDist x y = 1 := by simp [uniformMetric_dist, h]

end CompetitivePaging.Combining
end


/- Inlined checked module: ShuttleAlgorithms -/
section
set_option autoImplicit false

namespace CompetitivePaging.Combining.Shuttle

abbrev Page (m : ℕ) := Fin m × Bool
instance (m : ℕ) : MetricSpace (Page m) := uniformMetric (Page m)

theorem page_card (m : ℕ) : Fintype.card (Page m) = 2 * m := by
  change Fintype.card (Fin m × Bool) = 2 * m
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, Nat.mul_comm]

theorem page_uniform {m : ℕ} (x y : Page m) (h : x ≠ y) : dist x y = 1 :=
  uniformMetric_dist_of_ne _ x y h

theorem page_dist_le {m : ℕ} (x y : Page m) : dist x y ≤ 1 := by
  change (if x = y then (0 : ℝ) else 1) ≤ 1
  split_ifs <;> norm_num

abbrev StaticPage {m : ℕ} (i : Fin m) := {p : Page m // p ≠ (i, true)}

noncomputable instance {m : ℕ} (i : Fin m) : Fintype (StaticPage i) := Fintype.ofFinite _

theorem static_card {m : ℕ} (i : Fin m) : Fintype.card (StaticPage i) = 2 * m - 1 := by
  change Fintype.card {p : Page m // ¬p = (i, true)} = _
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, page_card]

noncomputable def labels {m : ℕ} (i : Fin m) : Fin (2 * m - 1) ≃ StaticPage i :=
  Fintype.equivOfCardEq (by rw [Fintype.card_fin, static_card])

noncomputable def initial {m : ℕ} (i : Fin m) : KServer.Config (2 * m - 1) (Page m) :=
  fun j => (labels i j).val

noncomputable def movingLabel {m : ℕ} (i : Fin m) : Fin (2 * m - 1) :=
  (labels i).symm ⟨(i, false), by simp⟩

theorem initial_movingLabel {m : ℕ} (i : Fin m) : initial i (movingLabel i) = (i, false) := by
  simp [initial, movingLabel]

def lastSide {m : ℕ} (i : Fin m) (l : List (Page m)) : Bool :=
  l.foldl (fun b r => if r.1 = i then r.2 else b) false

theorem lastSide_append {m : ℕ} (i : Fin m) (l : List (Page m)) (r : Page m) :
    lastSide i (l ++ [r]) = if r.1 = i then r.2 else lastSide i l := by
  simp [lastSide, List.foldl_append]

noncomputable def configuration {m : ℕ} (i : Fin m) (l : List (Page m)) :
    KServer.Config (2 * m - 1) (Page m) :=
  Function.update (initial i) (movingLabel i) (i, lastSide i l)

theorem configuration_serves {m : ℕ} (i : Fin m) (l : List (Page m)) (r : Page m) :
    ∃ j, configuration i (l ++ [r]) j = r := by
  by_cases hr : r.1 = i
  · refine ⟨movingLabel i, ?_⟩
    simp only [configuration, Function.update_self, lastSide_append, if_pos hr]
    exact Prod.ext hr.symm rfl
  · have hrt : r ≠ (i, true) := fun h => hr (congrArg Prod.fst h)
    let j := (labels i).symm ⟨r, hrt⟩
    have hj : initial i j = r := by simp [initial, j]
    have hne : j ≠ movingLabel i := by
      intro h
      have hh : r = (i, false) := hj.symm.trans (h ▸ initial_movingLabel i)
      exact hr (congrArg Prod.fst hh)
    exact ⟨j, by simpa only [configuration, Function.update_of_ne hne] using hj⟩

noncomputable def algorithm {m : ℕ} (i : Fin m) : KServer.OnlineAlgorithm (2 * m - 1) (Page m) where
  conf := configuration i
  serves := configuration_serves i

theorem moveCost_same_label {k : ℕ} {M : Type*} [MetricSpace M]
    (C : KServer.Config k M) (j : Fin k) (x y : M) :
    KServer.moveCost (Function.update C j x) (Function.update C j y) = dist x y := by
  unfold KServer.moveCost
  rw [Finset.sum_eq_single j]
  · simp
  · intro a _ haj
    simp [Function.update_of_ne haj]
  · intro hj
    exact False.elim (hj (Finset.mem_univ j))

theorem step_cost_le {m : ℕ} (i : Fin m) (l : List (Page m)) (r : Page m) :
    KServer.moveCost ((algorithm i).conf l) ((algorithm i).conf (l ++ [r])) ≤
      if r.1 = i then 1 else 0 := by
  change KServer.moveCost (Function.update _ _ _) (Function.update _ _ _) ≤ _
  rw [moveCost_same_label, lastSide_append]
  by_cases hr : r.1 = i
  · rw [if_pos hr, if_pos hr]
    exact page_dist_le _ _
  · simp [hr]

/-- The comparator family collectively moves at most one server at each request. -/
theorem total_cost_le_length {m : ℕ} (l : List (Page m)) :
    (∑ i, (algorithm i).cost l) ≤ (l.length : ℝ) := by
  induction l using List.reverseRecOn with
  | nil => simp [cost_nil]
  | append_singleton l r ih =>
    simp_rw [cost_append]
    rw [Finset.sum_add_distrib]
    have hstep : (∑ i, KServer.moveCost ((algorithm i).conf l)
        ((algorithm i).conf (l ++ [r]))) ≤ 1 := by
      calc
        _ ≤ ∑ i, if r.1 = i then (1 : ℝ) else 0 :=
          Finset.sum_le_sum (fun i _ => step_cost_le i l r)
        _ = 1 := by simp
    simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
    linarith

end CompetitivePaging.Combining.Shuttle
end


/- Inlined checked module: ForcingAdversary -/
section
set_option autoImplicit false

namespace CompetitivePaging.Combining

theorem exists_uncovered {k : ℕ} {M : Type*} [Fintype M]
    (hk : k < Fintype.card M) (C : KServer.Config k M) :
    ∃ r, ∀ j, C j ≠ r := by
  classical
  have hn : ¬Function.Surjective C := by
    intro h
    have hcard := Fintype.card_le_of_surjective C h
    simp only [Fintype.card_fin] at hcard
    omega
  simpa only [Function.Surjective, not_forall, not_exists] using hn

noncomputable def uncovered {k : ℕ} {M : Type*} [Fintype M]
    (hk : k < Fintype.card M) (C : KServer.Config k M) : M :=
  (exists_uncovered hk C).choose

theorem uncovered_ne {k : ℕ} {M : Type*} [Fintype M]
    (hk : k < Fintype.card M) (C : KServer.Config k M) (j : Fin k) :
    C j ≠ uncovered hk C := (exists_uncovered hk C).choose_spec j

noncomputable def forcingSequence {k : ℕ} {M : Type*} [MetricSpace M] [Fintype M]
    (hk : k < Fintype.card M) (A : KServer.OnlineAlgorithm k M) : ℕ → List M
  | 0 => []
  | N + 1 => let l := forcingSequence hk A N
    l ++ [uncovered hk (A.conf l)]

theorem forcingSequence_length {k : ℕ} {M : Type*} [MetricSpace M] [Fintype M]
    (hk : k < Fintype.card M) (A : KServer.OnlineAlgorithm k M) (N : ℕ) :
    (forcingSequence hk A N).length = N := by
  induction N with
  | zero => rfl
  | succ N ih => simp [forcingSequence, ih]

theorem forcingSequence_cost {k : ℕ} {M : Type*} [MetricSpace M] [Fintype M]
    (huniform : ∀ x y : M, x ≠ y → dist x y = 1)
    (hk : k < Fintype.card M) (A : KServer.OnlineAlgorithm k M) (N : ℕ) :
    (N : ℝ) ≤ A.cost (forcingSequence hk A N) := by
  induction N with
  | zero => simp [forcingSequence, cost_nil]
  | succ N ih =>
    let l := forcingSequence hk A N
    let r := uncovered hk (A.conf l)
    obtain ⟨j, hj⟩ := A.serves l r
    have hmove : 1 ≤ KServer.moveCost (A.conf l) (A.conf (l ++ [r])) := by
      calc
        (1 : ℝ) = dist (A.conf l j) (A.conf (l ++ [r]) j) := by
          rw [hj]
          exact (huniform _ _ (uncovered_ne hk (A.conf l) j)).symm
        _ ≤ ∑ a, dist (A.conf l a) (A.conf (l ++ [r]) a) :=
          Finset.single_le_sum (fun _ _ => dist_nonneg) (Finset.mem_univ j)
    change (N + 1 : ℕ) ≤ A.cost (l ++ [r])
    rw [cost_append, Nat.cast_add, Nat.cast_one]
    change (N : ℝ) ≤ A.cost l at ih
    linarith

end CompetitivePaging.Combining
end


/- Inlined checked module: RealizableNecessity -/
section
set_option autoImplicit false

namespace CompetitivePaging.Combining

theorem reciprocal_sum_le_of_realizable {m : ℕ} (hm : 0 < m)
    (c : Fin m → ℝ) (hc : ∀ i, 0 < c i) (hreal : Realizable c) :
    ∑ i, 1 / c i ≤ 1 := by
  classical
  obtain ⟨A, hA⟩ := hreal (2 * m - 1) (Shuttle.Page m) Shuttle.page_uniform Shuttle.algorithm
  choose a ha using hA
  by_contra hsum
  have hsum' : 1 < ∑ i, 1 / c i := lt_of_not_ge hsum
  let S := ∑ i, 1 / c i
  let K := ∑ i, a i / c i
  have hpos : 0 < S - 1 := by dsimp [S]; linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (K / (S - 1))
  have hk : 2 * m - 1 < Fintype.card (Shuttle.Page m) := by rw [Shuttle.page_card]; omega
  let l := forcingSequence hk A N
  have hAl : (N : ℝ) ≤ A.cost l := forcingSequence_cost Shuttle.page_uniform hk A N
  have hBl : (∑ i, (Shuttle.algorithm i).cost l) ≤ (N : ℝ) := by
    have h := Shuttle.total_cost_le_length l
    simpa only [l, forcingSequence_length] using h
  have hdiv (i : Fin m) : A.cost l * (1 / c i) ≤
      (Shuttle.algorithm i).cost l + a i / c i := by
    calc
      A.cost l * (1 / c i) = A.cost l / c i := by ring
      _ ≤ (c i * (Shuttle.algorithm i).cost l + a i) / c i :=
        div_le_div_of_nonneg_right (ha i l) (hc i).le
      _ = (Shuttle.algorithm i).cost l + a i / c i := by
        rw [add_div, mul_div_cancel_left₀ _ (hc i).ne']
  have htotal : A.cost l * S ≤ (N : ℝ) + K := by
    calc
      A.cost l * S = ∑ i, A.cost l * (1 / c i) := by dsimp [S]; rw [Finset.mul_sum]
      _ ≤ ∑ i, ((Shuttle.algorithm i).cost l + a i / c i) :=
        Finset.sum_le_sum (fun i _ => hdiv i)
      _ = (∑ i, (Shuttle.algorithm i).cost l) + K := by rw [Finset.sum_add_distrib]
      _ ≤ (N : ℝ) + K := add_le_add hBl le_rfl
  have hlarge : K < (N : ℝ) * (S - 1) := (div_lt_iff₀ hpos).mp hN
  have hS : 0 < S := by linarith
  have hNS := mul_le_mul_of_nonneg_right hAl hS.le
  nlinarith

end CompetitivePaging.Combining
end


/- Inlined checked module: PagingRoot -/
section
set_option autoImplicit false

namespace CompetitivePaging.Combining

/-- **Theorem 6** (Fiat, Karp, Luby, McGeoch, Sleator, Young 1991, p. 9). A sequence
`c = (c(1), …, c(m))` of positive reals is realizable if and only if `∑_{i} 1 / c(i) ≤ 1`. -/
theorem realizable_iff {m : ℕ} (hm : 0 < m) (c : Fin m → ℝ) (hc : ∀ i, 0 < c i) :
    Realizable c ↔ ∑ i, 1 / c i ≤ 1 := by
  constructor
  · exact reciprocal_sum_le_of_realizable hm c hc
  · exact realizable_of_reciprocal_sum_le hm c hc

end CompetitivePaging.Combining
end


open CompetitivePaging.Combining

theorem solution {m : ℕ} (hm : 0 < m) (c : Fin m → ℝ) (hc : ∀ i, 0 < c i) :
    Realizable c ↔ ∑ i, 1 / c i ≤ 1 := CompetitivePaging.Combining.realizable_iff hm c hc
