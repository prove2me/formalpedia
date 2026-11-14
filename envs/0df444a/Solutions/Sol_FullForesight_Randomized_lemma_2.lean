-- Prove2me | solution 1 for FullForesight.Randomized.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:58:59.253247+00:00
-- url     : https://prove2.me/submissions/20e47f28-b494-491a-b4e8-8c6f98283dde

import Mathlib
import Definitions.Def_SubsamplingSM_Offline_IsSubmodular
import Definitions.Def_SubsamplingSM_Offline_IsMonotoneSetFn
import Definitions.Def_FullForesight_Randomized_AdditionRobust
import Definitions.Def_FullForesight_Randomized_IntervalSelection
import Definitions.Def_ConsistentSubmodular_MainStatements
import Theorems.Thm_ConsistentSubmodular_intervalSelectionReduction

/-!
# Bridge for Lemma 2 (from interval selection to addition robustness)

The mission's statement lives on an arbitrary type `X`; the source development's
`WindowInstance n` lives on `Fin n`. The instance is transported along an embedding
`Fin n ↪ X` whose range is the finite ground set `Vnow ∪ {v₁, …, v_m}`.
-/

namespace FullForesight.Randomized.Bridge

open ConsistentSubmodular

noncomputable section

variable {X : Type} [DecidableEq X] {m : ℕ}

/-- Diminishing returns implies the lattice form of submodularity. -/
theorem lattice_of_dr {α : Type*} [DecidableEq α] (f : Finset α → ℝ)
    (h : SubsamplingSM.Offline.IsSubmodular f) (A B : Finset α) :
    f (A ∪ B) + f (A ∩ B) ≤ f A + f B := by
  have key : ∀ (D S T : Finset α), S ⊆ T → Disjoint D T →
      f (T ∪ D) - f T ≤ f (S ∪ D) - f S := by
    intro D
    induction D using Finset.induction_on with
    | empty => intro S T _ _; simp
    | insert e D he ih =>
      intro S T hST hd
      rw [Finset.disjoint_insert_left] at hd
      have h1 := ih S T hST hd.2
      have h2 : f (insert e (T ∪ D)) - f (T ∪ D) ≤ f (insert e (S ∪ D)) - f (S ∪ D) :=
        h (S ∪ D) (T ∪ D) e (Finset.union_subset_union_left hST)
          (by simp [hd.1, he])
      have e1 : T ∪ insert e D = insert e (T ∪ D) := by
        ext x; simp only [Finset.mem_union, Finset.mem_insert]; tauto
      have e2 : S ∪ insert e D = insert e (S ∪ D) := by
        ext x; simp only [Finset.mem_union, Finset.mem_insert]; tauto
      rw [e1, e2]
      linarith
  have h1 := key (A \ B) (A ∩ B) B Finset.inter_subset_right Finset.sdiff_disjoint
  have e1 : B ∪ A \ B = A ∪ B := by
    ext x; simp only [Finset.mem_union, Finset.mem_sdiff]; tauto
  have e2 : A ∩ B ∪ A \ B = A := by
    ext x; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
  rw [e1, e2] at h1
  linarith

/-! ### The transport `Fin n ↪ X` -/

/-- The finite ground set `Vnow ∪ {v₁, …, v_m}`. -/
def ground (Vnow : Finset X) (v : Fin m → X) : Finset X := Vnow ∪ Finset.univ.image v

/-- An embedding of `Fin |G|` into `X` with range `G`. -/
def emb (G : Finset X) : Fin G.card ↪ X :=
  G.equivFin.symm.toEmbedding.trans (Function.Embedding.subtype _)

omit [DecidableEq X] in
theorem emb_mem (G : Finset X) (i : Fin G.card) : emb G i ∈ G := (G.equivFin.symm i).2

omit [DecidableEq X] in
theorem exists_emb (G : Finset X) {x : X} (hx : x ∈ G) : ∃ i, emb G i = x := by
  refine ⟨G.equivFin ⟨x, hx⟩, ?_⟩
  show ((G.equivFin.symm (G.equivFin ⟨x, hx⟩) : {y // y ∈ G}) : X) = x
  rw [Equiv.symm_apply_apply]

/-- The pull-back of a subset of `X` to `Fin |G|`. -/
def pb (G S : Finset X) : Finset (Fin G.card) := Finset.univ.filter (fun i => emb G i ∈ S)

theorem mem_pb {G S : Finset X} {i : Fin G.card} : i ∈ pb G S ↔ emb G i ∈ S := by
  unfold pb
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem map_pb {G S : Finset X} (hS : S ⊆ G) : (pb G S).map (emb G) = S := by
  ext x
  rw [Finset.mem_map]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact mem_pb.1 hi
  · intro hx
    obtain ⟨i, rfl⟩ := exists_emb G (hS hx)
    exact ⟨i, mem_pb.2 hx, rfl⟩

theorem pb_map {G : Finset X} (T : Finset (Fin G.card)) : pb G (T.map (emb G)) = T := by
  ext i
  rw [mem_pb, Finset.mem_map']

theorem pb_mono {G A B : Finset X} (h : A ⊆ B) : pb G A ⊆ pb G B :=
  fun _ hi => mem_pb.2 (h (mem_pb.1 hi))

theorem card_pb {G S : Finset X} (hS : S ⊆ G) : (pb G S).card = S.card := by
  rw [← Finset.card_map (emb G), map_pb hS]

theorem map_subset_of_subset_pb {G V : Finset X} {T : Finset (Fin G.card)} (h : T ⊆ pb G V) :
    T.map (emb G) ⊆ V := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := Finset.mem_map.1 hx
  exact mem_pb.1 (h hi)

theorem map_union_pb {G B : Finset X} (T : Finset (Fin G.card)) (hB : B ⊆ G) :
    (T ∪ pb G B).map (emb G) = T.map (emb G) ∪ B := by
  rw [Finset.map_union, map_pb hB]

/-! ### Prefixes and the benchmark -/

theorem prefixSet_zero (v : Fin m → X) : prefixSet v 0 = ∅ := by
  simp [prefixSet]

theorem prefixSet_mono (v : Fin m → X) {a b : ℕ} (h : a ≤ b) : prefixSet v a ⊆ prefixSet v b := by
  unfold prefixSet
  apply Finset.image_subset_image
  intro i hi
  rw [Finset.mem_filter] at hi ⊢
  exact ⟨hi.1, lt_of_lt_of_le hi.2 h⟩

theorem prefixSet_subset (Vnow : Finset X) (v : Fin m → X) (j : ℕ) :
    prefixSet v j ⊆ ground Vnow v :=
  fun _ hx => Finset.mem_union_right _ (Finset.image_subset_image (Finset.filter_subset _ _) hx)

theorem subset_ground {Vnow S : Finset X} (v : Fin m → X) (h : S ⊆ Vnow) : S ⊆ ground Vnow v :=
  h.trans Finset.subset_union_left

theorem prefixSet_not_mem {Vnow : Finset X} {v : Fin m → X} (h : ∀ i, v i ∉ Vnow) (j : ℕ)
    {x : X} (hx : x ∈ prefixSet v j) : x ∉ Vnow := by
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
  exact h i

theorem le_benchmark (f : Finset X → ℝ) (Vnow : Finset X) (v : Fin m → X) (κ j : ℕ)
    {O : Finset X} (hO : O ⊆ Vnow) (hc : O.card ≤ κ) :
    f (O ∪ prefixSet v j) ≤ benchmark f Vnow v κ j :=
  Finset.le_sup' (fun O => f (O ∪ prefixSet v j))
    (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hO, hc⟩)

/-! ### The transported instance -/

/-- The objective `A ↦ f (emb A)` on `Fin |G|`. -/
def toObjective (G : Finset X) (f : Finset X → ℝ) (h0 : ∀ S, 0 ≤ f S)
    (hm : SubsamplingSM.Offline.IsMonotoneSetFn f) (hs : SubsamplingSM.Offline.IsSubmodular f) :
    Objective G.card where
  value A := f (A.map (emb G))
  nonnegative A := h0 _
  monotone A B h := hm _ _ (Finset.map_subset_map.2 h)
  submodular A B := by
    rw [Finset.map_union, Finset.map_inter]
    exact lattice_of_dr f hs _ _

/-- An instance of the mission with a family of prefix optimizers, as a `WindowInstance` of the
source development. -/
def toWindow (f : Finset X → ℝ) (Vnow : Finset X) (v : Fin m → X) (κ : ℕ)
    (O : Fin (m + 1) → Finset X) (hinst : IsARInstance f Vnow v)
    (hO : IsMaximizerFamily f Vnow v κ O) : WindowInstance (ground Vnow v).card where
  objective := toObjective (ground Vnow v) f hinst.1 hinst.2.1 hinst.2.2.1
  present := pb (ground Vnow v) Vnow
  coreBudget := κ
  lastStage := m
  arrivals j := pb (ground Vnow v) (prefixSet v j)
  candidate j := pb (ground Vnow v) (O j)
  arrivals_zero := by
    show pb (ground Vnow v) (prefixSet v ((0 : Fin (m + 1)) : ℕ)) = ∅
    rw [Fin.val_zero, prefixSet_zero]
    ext i
    simp [mem_pb]
  arrivals_mono := fun _ _ hab => pb_mono (prefixSet_mono v (Fin.le_def.1 hab))
  arrivals_disjoint := fun j => Finset.disjoint_left.2 fun _ hi hi' =>
    prefixSet_not_mem hinst.2.2.2.2 j (mem_pb.1 hi) (mem_pb.1 hi')
  candidate_subset := fun j => pb_mono (hO j).1
  candidate_card := fun j => by
    rw [card_pb (subset_ground v (hO j).1)]
    exact (hO j).2.1
  candidate_optimal := fun j O' hO' hc => by
    show f ((O' ∪ pb (ground Vnow v) (prefixSet v j)).map (emb _)) ≤
      f ((pb (ground Vnow v) (O j) ∪ pb (ground Vnow v) (prefixSet v j)).map (emb _))
    rw [map_union_pb _ (prefixSet_subset Vnow v j), map_union_pb _ (prefixSet_subset Vnow v j),
      map_pb (subset_ground v (hO j).1), (hO j).2.2]
    exact le_benchmark f Vnow v κ j (map_subset_of_subset_pb hO')
      (by rw [Finset.card_map]; exact hc)

theorem value_eq (f : Finset X → ℝ) (Vnow : Finset X) (v : Fin m → X) (κ : ℕ)
    (O : Fin (m + 1) → Finset X) (hinst : IsARInstance f Vnow v)
    (hO : IsMaximizerFamily f Vnow v κ O) (i j : Fin (m + 1)) :
    (toWindow f Vnow v κ O hinst hO).objective.value
      ((toWindow f Vnow v κ O hinst hO).candidate i ∪
        (toWindow f Vnow v κ O hinst hO).arrivals j) = f (O i ∪ prefixSet v j) := by
  show f ((pb (ground Vnow v) (O i) ∪ pb (ground Vnow v) (prefixSet v j)).map (emb _)) = _
  rw [map_union_pb _ (prefixSet_subset Vnow v j),
    map_pb (subset_ground v (hO i).1)]

/-! ### Lemma 2 -/

theorem isIntervalInstance {N : ℕ} (I : IntervalInstance N) :
    IsIntervalInstance I.left I.right I.prob :=
  ⟨fun i => ⟨I.left_nonneg i, I.left_le_right i⟩, I.prob_nonneg, I.prob_sum⟩

theorem gap_eq {N : ℕ} (I : IntervalInstance N) :
    gap I.left I.right I.prob = I.adaptivityGap := rfl

/-- The benchmark is attained. -/
theorem exists_maximizer (f : Finset X → ℝ) (Vnow : Finset X) (v : Fin m → X) (κ j : ℕ) :
    ∃ O : Finset X, O ⊆ Vnow ∧ O.card ≤ κ ∧
      f (O ∪ prefixSet v j) = benchmark f Vnow v κ j := by
  obtain ⟨O, hO, hEq⟩ := Finset.exists_mem_eq_sup'
    (s := Vnow.powerset.filter (fun O => O.card ≤ κ)) ⟨∅, by simp⟩
    (fun O => f (O ∪ prefixSet v j))
  rw [Finset.mem_filter, Finset.mem_powerset] at hO
  exact ⟨O, hO.1, hO.2, hEq.symm⟩

theorem exists_maximizerFamily (f : Finset X → ℝ) (Vnow : Finset X) (v : Fin m → X) (κ : ℕ) :
    ∃ O : Fin (m + 1) → Finset X, IsMaximizerFamily f Vnow v κ O := by
  choose O hO using fun j : Fin (m + 1) => exists_maximizer f Vnow v κ (j : ℕ)
  exact ⟨O, hO⟩

/-- Weights supported below `pb G V` sum the same way over `V.powerset` and over all subsets of
`Fin |G|`. -/
theorem sum_transport {G V : Finset X} (hV : V ⊆ G) (w : Finset (Fin G.card) → ℝ)
    (hw : ∀ T, w T ≠ 0 → T ⊆ pb G V) (g : Finset X → ℝ) :
    ∑ S ∈ V.powerset, w (pb G S) * g S = ∑ T, w T * g (T.map (emb G)) := by
  have h1 : ∑ T ∈ (pb G V).powerset, w T * g (T.map (emb G)) =
      ∑ T, w T * g (T.map (emb G)) := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro T _ hT
    have h0 : w T = 0 := by
      by_contra h0
      exact hT (Finset.mem_powerset.2 (hw T h0))
    rw [h0, zero_mul]
  rw [← h1]
  refine Finset.sum_nbij' (fun S => pb G S) (fun T => T.map (emb G)) ?_ ?_ ?_ ?_ ?_
  · intro S hS
    exact Finset.mem_powerset.2 (pb_mono (Finset.mem_powerset.1 hS))
  · intro T hT
    exact Finset.mem_powerset.2 (map_subset_of_subset_pb (Finset.mem_powerset.1 hT))
  · intro S hS
    exact map_pb ((Finset.mem_powerset.1 hS).trans hV)
  · intro T _
    exact pb_map T
  · intro S hS
    rw [map_pb ((Finset.mem_powerset.1 hS).trans hV)]

theorem lemma_2_bridge (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (h : ∀ (N : ℕ) (ℓ r p : Fin (N + 1) → ℝ), IsIntervalInstance ℓ r p → α ≤ gap ℓ r p)
    (f : Finset X → ℝ) (Vnow : Finset X) (v : Fin m → X) (κ : ℕ)
    (hinst : IsARInstance f Vnow v) : ∃ μ : Finset X → ℝ, IsRobustDist f Vnow v κ α μ := by
  obtain ⟨O, hO⟩ := exists_maximizerFamily f Vnow v κ
  obtain ⟨w, hw0, hw1, hws, hwr⟩ := ConsistentSubmodular.intervalSelectionReduction α hα.1 hα.2
    (fun N I => (gap_eq I) ▸ h N I.left I.right I.prob (isIntervalInstance I)) _
    (toWindow f Vnow v κ O hinst hO)
  have hV : Vnow ⊆ ground Vnow v := Finset.subset_union_left
  have hsupp : ∀ T, w T ≠ 0 → T ⊆ pb (ground Vnow v) Vnow := fun T hT => (hws T hT).1
  refine ⟨fun S => w (pb (ground Vnow v) S), fun S _ => hw0 _, ?_, ?_, ?_⟩
  · have hsum := sum_transport hV w hsupp (fun _ => 1)
    simp only [mul_one] at hsum
    rw [hsum]
    exact hw1
  · intro S hS hpos
    have hc := (hws _ (ne_of_gt hpos)).2
    rw [card_pb ((Finset.mem_powerset.1 hS).trans hV)] at hc
    exact hc
  · intro j
    have hb : (toWindow f Vnow v κ O hinst hO).benchmark j = benchmark f Vnow v κ j :=
      (value_eq f Vnow v κ O hinst hO j j).trans (hO j).2.2
    show α * benchmark f Vnow v κ j ≤
      ∑ S ∈ Vnow.powerset, w (pb (ground Vnow v) S) * f (S ∪ prefixSet v j)
    rw [sum_transport hV w hsupp (fun S => f (S ∪ prefixSet v j)), ← hb]
    refine (hwr j).trans (le_of_eq (Finset.sum_congr rfl fun T _ => ?_))
    show w T * f ((T ∪ pb (ground Vnow v) (prefixSet v j)).map (emb _)) =
      w T * f (T.map (emb _) ∪ prefixSet v j)
    rw [map_union_pb _ (prefixSet_subset Vnow v j)]

end

end FullForesight.Randomized.Bridge

open FullForesight.Randomized in
theorem solution (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (h : ∀ (N : ℕ) (ℓ r p : Fin (N + 1) → ℝ), IsIntervalInstance ℓ r p → α ≤ gap ℓ r p) :
    ∀ (X : Type) [DecidableEq X] (m : ℕ) (f : Finset X → ℝ) (Vnow : Finset X) (v : Fin m → X)
      (κ : ℕ), IsARInstance f Vnow v → ∃ μ : Finset X → ℝ, IsRobustDist f Vnow v κ α μ :=
  fun _ _ _ f Vnow v κ hinst => Bridge.lemma_2_bridge α hα h f Vnow v κ hinst
