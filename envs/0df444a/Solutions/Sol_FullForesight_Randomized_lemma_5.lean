-- Prove2me | solution 1 for FullForesight.Randomized.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:57:17.611204+00:00
-- url     : https://prove2.me/submissions/e63308d2-a431-489a-b808-429478a8dcfe

import Mathlib
import Definitions.Def_SubsamplingSM_Offline_IsSubmodular
import Definitions.Def_SubsamplingSM_Offline_IsMonotoneSetFn
import Definitions.Def_FullForesight_Randomized_AdditionRobust
import Definitions.Def_ConsistentSubmodular_MainStatements
import Theorems.Thm_ConsistentSubmodular_minimax

/-!
# Bridge for Lemma 5 (finite minimax duality)

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

/-! ### Lemma 5 -/

theorem payoff_eq (f : Finset X → ℝ) (Vnow : Finset X) (v : Fin m → X) (κ : ℕ)
    (O : Fin (m + 1) → Finset X) (hinst : IsARInstance f Vnow v)
    (hO : IsMaximizerFamily f Vnow v κ O) :
    (toWindow f Vnow v κ O hinst hO).payoff = payoff f v O := by
  funext i j
  exact congrArg₂ (· / ·) (value_eq f Vnow v κ O hinst hO i j) (value_eq f Vnow v κ O hinst hO j j)

theorem lpValue_eq (f : Finset X → ℝ) (Vnow : Finset X) (v : Fin m → X) (κ : ℕ)
    (O : Fin (m + 1) → Finset X) (hinst : IsARInstance f Vnow v)
    (hO : IsMaximizerFamily f Vnow v κ O) :
    (toWindow f Vnow v κ O hinst hO).lpValue = lpValue f v O := by
  have hv := value_eq f Vnow v κ O hinst hO
  show sSup {ρ : ℝ | 0 ≤ ρ ∧ ρ ≤ 1 ∧ ∃ a : Fin (m + 1) → ℝ, IsSimplex a ∧
      ∀ j : Fin (m + 1), ρ * (toWindow f Vnow v κ O hinst hO).objective.value
          ((toWindow f Vnow v κ O hinst hO).candidate j ∪
            (toWindow f Vnow v κ O hinst hO).arrivals j) ≤
        ∑ i : Fin (m + 1), a i * (toWindow f Vnow v κ O hinst hO).objective.value
          ((toWindow f Vnow v κ O hinst hO).candidate i ∪
            (toWindow f Vnow v κ O hinst hO).arrivals j)} = _
  simp only [hv]
  rfl

theorem lemma_5_bridge (f : Finset X → ℝ) (Vnow : Finset X)
    (v : Fin m → X) (κ : ℕ) (O : Fin (m + 1) → Finset X)
    (hinst : IsARInstance f Vnow v) (hO : IsMaximizerFamily f Vnow v κ O)
    (hκ : 1 ≤ κ) (hpos : 0 < f (O 0)) :
    IsGreatest {x : ℝ | ∃ a ∈ stdSimplex ℝ (Fin (m + 1)),
        x = Finset.univ.inf' Finset.univ_nonempty (fun j => ∑ i, a i * payoff f v O i j)}
        (lpValue f v O) ∧
      IsLeast {x : ℝ | ∃ b ∈ stdSimplex ℝ (Fin (m + 1)),
        x = Finset.univ.sup' Finset.univ_nonempty (fun i => ∑ j, b j * payoff f v O i j)}
        (lpValue f v O) := by
  have hpos' : 0 < (toWindow f Vnow v κ O hinst hO).objective.value
      ((toWindow f Vnow v κ O hinst hO).candidate 0) := by
    show 0 < f ((pb (ground Vnow v) (O 0)).map (emb _))
    rw [map_pb (subset_ground v (hO 0).1)]
    exact hpos
  obtain ⟨h1, h2⟩ := ConsistentSubmodular.minimax _ (toWindow f Vnow v κ O hinst hO) hκ hpos'
  rw [lpValue_eq, payoff_eq] at h1 h2
  exact ⟨h1, h2⟩

end

end FullForesight.Randomized.Bridge

open FullForesight.Randomized in
theorem solution {X : Type} [DecidableEq X] {m : ℕ} (f : Finset X → ℝ) (Vnow : Finset X)
    (v : Fin m → X) (κ : ℕ) (O : Fin (m + 1) → Finset X)
    (hinst : IsARInstance f Vnow v) (hO : IsMaximizerFamily f Vnow v κ O)
    (hκ : 1 ≤ κ) (hpos : 0 < f (O 0)) :
    IsGreatest {x : ℝ | ∃ a ∈ stdSimplex ℝ (Fin (m + 1)),
        x = Finset.univ.inf' Finset.univ_nonempty (fun j => ∑ i, a i * payoff f v O i j)}
        (lpValue f v O) ∧
      IsLeast {x : ℝ | ∃ b ∈ stdSimplex ℝ (Fin (m + 1)),
        x = Finset.univ.sup' Finset.univ_nonempty (fun i => ∑ j, b j * payoff f v O i j)}
        (lpValue f v O) :=
  Bridge.lemma_5_bridge f Vnow v κ O hinst hO hκ hpos
