-- Prove2me | solution 1 for ConantTerry.Orders.extraction_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T15:21:50.938109+00:00
-- url     : https://prove2.me/submissions/bcd4acb9-f524-4d86-9465-2d878da6636a

import Mathlib
import Definitions.Def_ConantTerry_Orders_extraction_height
import Theorems.Thm_ConantTerry_Orders_tree_ramsey
import Theorems.Thm_ConantTerry_Orders_restrict_tree
import Theorems.Thm_ConantTerry_Orders_tree_embedding_properties

section
set_option autoImplicit false
namespace ConantTerry.Dev.ExtractionRec
open ConantTerry.Orders

theorem exists_leaf {t : ℕ} (σ : WordsBelow t) (a : Bool) :
    ∃ η : WordsAt t, List.IsPrefix (σ.val ++ [a]) η.val := by
  have hσ := σ.2
  refine ⟨⟨σ.val ++ [a] ++ List.replicate (t - σ.val.length - 1) a, ?_⟩, ?_⟩
  · simp; omega
  · exact List.prefix_append _ _

theorem tree_left {X Y : Type*} {f : X × Y → Set.Icc (0 : ℝ) 1} {t : ℕ} {γ : ℝ}
    {x : WordsBelow t → X} {y : WordsAt t → Y} {r : WordsBelow t → Set.Icc (0 : ℝ) 1}
    (hT : IsFunctionTree f t γ x y r) (σ : WordsBelow t) (η : WordsAt t)
    (h : List.IsPrefix (σ.val ++ [false]) η.val) :
    (f (x σ, y η) : ℝ) ≤ (r σ : ℝ) := by
  obtain ⟨η', h'⟩ := exists_leaf σ true
  exact (hT σ η η' h h').1

theorem tree_right {X Y : Type*} {f : X × Y → Set.Icc (0 : ℝ) 1} {t : ℕ} {γ : ℝ}
    {x : WordsBelow t → X} {y : WordsAt t → Y} {r : WordsBelow t → Set.Icc (0 : ℝ) 1}
    (hT : IsFunctionTree f t γ x y r) (σ : WordsBelow t) (η : WordsAt t)
    (h : List.IsPrefix (σ.val ++ [true]) η.val) :
    (r σ : ℝ) + γ ≤ (f (x σ, y η) : ℝ) := by
  obtain ⟨η', h'⟩ := exists_leaf σ false
  exact (hT σ η' η h' h).2

theorem eh_le {X Y : Type*} (f : X × Y → Set.Icc (0 : ℝ) 1) (δ : ℝ) (k ℓ t : ℕ)
    (ht : 1 ≤ t) (h : ExtractionP f δ k ℓ t) :
    extractionHeight f δ k ℓ ≤ (t : WithTop ℕ) := by
  classical
  have hex : ∃ t : ℕ, 1 ≤ t ∧ ExtractionP f δ k ℓ t := ⟨t, ht, h⟩
  unfold extractionHeight
  rw [dif_pos hex]
  exact_mod_cast Nat.find_min' hex ⟨ht, h⟩

theorem eh_ne_top {X Y : Type*} (f : X × Y → Set.Icc (0 : ℝ) 1) (δ : ℝ) (k ℓ : ℕ)
    (h : extractionHeight f δ k ℓ ≠ ⊤) :
    ∃ n : ℕ, extractionHeight f δ k ℓ = (n : WithTop ℕ) ∧ 1 ≤ n ∧ ExtractionP f δ k ℓ n := by
  classical
  by_cases hex : ∃ t : ℕ, 1 ≤ t ∧ ExtractionP f δ k ℓ t
  · refine ⟨Nat.find hex, ?_, (Nat.find_spec hex).1, (Nat.find_spec hex).2⟩
    unfold extractionHeight
    rw [dif_pos hex]
  · exfalso; apply h
    unfold extractionHeight
    rw [dif_neg hex]

theorem eh_eq_one {X Y : Type*} (f : X × Y → Set.Icc (0 : ℝ) 1) (δ : ℝ) (k ℓ : ℕ)
    (h : ExtractionP f δ k ℓ 1) : extractionHeight f δ k ℓ = 1 := by
  have hle := eh_le f δ k ℓ 1 le_rfl h
  have hne : extractionHeight f δ k ℓ ≠ ⊤ :=
    ne_top_of_le_ne_top (WithTop.coe_ne_top) hle
  obtain ⟨n, hn, h1, _⟩ := eh_ne_top f δ k ℓ hne
  apply le_antisymm
  · simpa using hle
  · rw [hn]; exact_mod_cast h1

theorem P_one_left {X Y : Type*} (f : X × Y → Set.Icc (0 : ℝ) 1) (δ : ℝ) (hδ : 0 < δ)
    (k : ℕ) : ExtractionP f δ k 1 1 := by
  intro x y r hT
  right
  refine ⟨fun _ => ⟨[], by simp⟩, fun _ => ⟨[false], by simp⟩, ?_⟩
  intro i j
  have hij : i = j := Subsingleton.elim _ _
  subst hij
  refine ⟨fun _ => ?_, fun h => absurd h (lt_irrefl _)⟩
  have := tree_left hT ⟨[], by simp⟩ ⟨[false], by simp⟩ (by simp)
  linarith

theorem P_one_right {X Y : Type*} (f : X × Y → Set.Icc (0 : ℝ) 1) (δ : ℝ) (hδ : 0 < δ)
    (ℓ : ℕ) : ExtractionP f δ 1 ℓ 1 := by
  intro x y r hT
  left
  refine ⟨fun _ => ⟨[], by simp⟩, fun _ => ⟨[true], by simp⟩, ?_⟩
  intro i j
  have hij : i = j := Subsingleton.elim _ _
  subst hij
  refine ⟨fun _ => ?_, fun h => absurd h (lt_irrefl _)⟩
  have := tree_right hT ⟨[], by simp⟩ ⟨[true], by simp⟩ (by simp)
  linarith

def consAM (n : ℕ) (u : Bool) (σ : WordsAtMost n) : WordsAtMost (n + 1) :=
  ⟨u :: σ.val, by
    have h : σ.val.length ≤ n := σ.2
    show (u :: σ.val).length ≤ n + 1
    simp; omega⟩

def consB (n : ℕ) (u : Bool) (σ : WordsBelow n) : WordsBelow (n + 1) :=
  ⟨u :: σ.val, by
    have h : σ.val.length < n := σ.2
    show (u :: σ.val).length < n + 1
    simp; omega⟩

def rootB (n : ℕ) (hn : 1 ≤ n) : WordsBelow n := ⟨[], by simp; omega⟩

/-- The restriction step: from a tree embedding of height `n+1` build a function tree of height `n`. -/
theorem step {X Y : Type*} (f : X × Y → Set.Icc (0 : ℝ) 1) (δ : ℝ) (hδ : 0 < δ)
    (t n : ℕ) (hn : 1 ≤ n) (ht : 1 ≤ t)
    (x : WordsBelow t → X) (y : WordsAt t → Y) (r : WordsBelow t → Set.Icc (0 : ℝ) 1)
    (hT : IsFunctionTree f t (2 * δ) x y r) (u : Bool)
    (ϕ : WordsBelow (n + 1) → WordsBelow t) (hϕ : IsTreeEmbedding ϕ) :
    ∃ (nodes : WordsBelow n → WordsBelow t) (leaves : WordsAt n → WordsAt t),
      IsFunctionTree f n (2 * δ) (x ∘ nodes) (y ∘ leaves) (r ∘ nodes) ∧
      (∀ σ, nodes σ ∈ Set.range ϕ) ∧
      ∃ ρ : WordsBelow t, ρ ∈ Set.range ϕ ∧
        ∀ η : WordsAt n, List.IsPrefix (ρ.val ++ [u]) (leaves η).val := by
  obtain ⟨ψ, hψ, hψn⟩ := (tree_embedding_properties.2.2.2) (n + 1) t (by omega) ht ϕ hϕ
  let ψu : WordsAtMost n → WordsAtMost t := fun σ => ψ (consAM n u σ)
  have hψu : IsProperEmbedding ψu := by
    refine ⟨?_, ?_⟩
    · intro σ τ a h
      exact hψ.1 (consAM n u σ) (consAM n u τ) a (by simpa [consAM] using h)
    · intro σ hσ
      exact hψ.2 (consAM n u σ) (by simp [consAM, hσ])
  obtain ⟨nodes, leaves, hnodes, hleaves, hT'⟩ :=
    restrict_tree f n t hn ht (2 * δ) (by linarith) x y r hT ψu hψu
  refine ⟨nodes, leaves, hT', ?_, ?_⟩
  · intro σ
    refine ⟨consB n u σ, ?_⟩
    apply Subtype.ext
    rw [hnodes σ]
    exact (hψn (consB n u σ)).symm
  · refine ⟨ϕ (rootB (n+1) (by omega)), ⟨_, rfl⟩, ?_⟩
    intro η
    rw [hleaves η]
    have := hψ.1 (nodeInclusion (rootB (n + 1) (by omega))) (consAM n u (leafInclusion η)) u
      (by simp [nodeInclusion, rootB, consAM, leafInclusion])
    rw [hψn (rootB (n+1) (by omega))] at this
    exact this


theorem ramsey2 {t t1 t2 : ℕ} (ht : t = t1 + t2 + 1) (P0 P1 : Set (WordsBelow t))
    (hc : ∀ σ, σ ∈ P0 ∨ σ ∈ P1) :
    (∃ ϕ : WordsBelow (t1 + 1) → WordsBelow t, IsTreeEmbedding ϕ ∧ Set.range ϕ ⊆ P0) ∨
    (∃ ϕ : WordsBelow (t2 + 1) → WordsBelow t, IsTreeEmbedding ϕ ∧ Set.range ϕ ⊆ P1) := by
  obtain ⟨i, ϕ, h1, h2⟩ := tree_ramsey 2 t (by omega) (by omega) ![t1 + 1, t2 + 1]
    (by intro i; fin_cases i <;> simp) (by subst ht; simp [Fin.sum_univ_two]; omega)
    ![P0, P1] (by
      intro σ
      rcases hc σ with h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩)
  fin_cases i
  · exact Or.inl ⟨ϕ, h1, h2⟩
  · exact Or.inr ⟨ϕ, h1, h2⟩

theorem core {X Y : Type*} (f : X × Y → Set.Icc (0 : ℝ) 1) (δ : ℝ) (hδ : 0 < δ)
    (K L t1 t2 : ℕ) (h1 : 1 ≤ t1) (h2 : 1 ≤ t2)
    (hP1 : ExtractionP f δ K (L + 1) t1) (hP2 : ExtractionP f δ (K + 1) L t2) :
    ExtractionP f δ (K + 1) (L + 1) (t1 + t2 + 1) := by
  intro x y r hT
  have ht : 1 ≤ t1 + t2 + 1 := by omega
  let ηs : WordsAt (t1 + t2 + 1) := ⟨List.replicate (t1 + t2 + 1) false, by simp⟩
  rcases ramsey2 (t := t1 + t2 + 1) rfl
      {σ | (r σ : ℝ) + δ ≤ (f (x σ, y ηs) : ℝ)}
      {σ | (f (x σ, y ηs) : ℝ) < (r σ : ℝ) + δ}
      (fun σ => by
        by_cases h : (r σ : ℝ) + δ ≤ (f (x σ, y ηs) : ℝ)
        · exact Or.inl h
        · exact Or.inr (not_le.mp h)) with ⟨ϕ, hϕ, hr⟩ | ⟨ϕ, hϕ, hr⟩
  · obtain ⟨nodes, leaves, hT', hrange, ρ, hρ, hleaf⟩ :=
      step f δ hδ (t1 + t2 + 1) t1 h1 ht x y r hT false ϕ hϕ
    have hP0 : ∀ σ ∈ Set.range ϕ, (r σ : ℝ) + δ ≤ (f (x σ, y ηs) : ℝ) :=
      fun σ hσ => hr hσ
    rcases hP1 _ _ _ hT' with ⟨α', β', h⟩ | ⟨α', β', h⟩
    · left
      refine ⟨Fin.cons ρ (fun i => nodes (α' i)), Fin.cons ηs (fun i => leaves (β' i)), ?_⟩
      intro i j
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero =>
          simp only [Fin.cons_zero]
          exact ⟨fun _ => hP0 ρ hρ, fun h => absurd h (lt_irrefl _)⟩
        | succ j' =>
          simp only [Fin.cons_zero, Fin.cons_succ]
          exact ⟨fun _ => hP0 _ (hrange (α' j')),
            fun _ => tree_left hT ρ _ (hleaf (β' j'))⟩
      | succ i' =>
        induction j using Fin.cases with
        | zero =>
          refine ⟨fun h => ?_, fun h => ?_⟩ <;> exact absurd h (by simp [Fin.le_def, Fin.lt_def])
        | succ j' =>
          simp only [Fin.cons_succ, Fin.succ_le_succ_iff, Fin.succ_lt_succ_iff]
          exact h i' j'
    · right
      exact ⟨fun i => nodes (α' i), fun i => leaves (β' i), h⟩
  · obtain ⟨nodes, leaves, hT', hrange, ρ, hρ, hleaf⟩ :=
      step f δ hδ (t1 + t2 + 1) t2 h2 ht x y r hT true ϕ hϕ
    have hP0 : ∀ σ ∈ Set.range ϕ, (f (x σ, y ηs) : ℝ) < (r σ : ℝ) + δ :=
      fun σ hσ => hr hσ
    rcases hP2 _ _ _ hT' with ⟨α', β', h⟩ | ⟨α', β', h⟩
    · left
      exact ⟨fun i => nodes (α' i), fun i => leaves (β' i), h⟩
    · right
      refine ⟨Fin.cons ρ (fun i => nodes (α' i)), Fin.cons ηs (fun i => leaves (β' i)), ?_⟩
      intro i j
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero =>
          simp only [Fin.cons_zero]
          exact ⟨fun _ => hP0 ρ hρ, fun h => absurd h (lt_irrefl _)⟩
        | succ j' =>
          simp only [Fin.cons_zero, Fin.cons_succ]
          exact ⟨fun _ => hP0 _ (hrange (α' j')),
            fun _ => tree_right hT ρ _ (hleaf (β' j'))⟩
      | succ i' =>
        induction j using Fin.cases with
        | zero =>
          refine ⟨fun h => ?_, fun h => ?_⟩ <;> exact absurd h (by simp [Fin.le_def, Fin.lt_def])
        | succ j' =>
          simp only [Fin.cons_succ, Fin.succ_le_succ_iff, Fin.succ_lt_succ_iff]
          exact h i' j'

end ConantTerry.Dev.ExtractionRec

namespace ConantTerry.Orders
open ConantTerry.Dev.ExtractionRec in
theorem chk_extraction_recurrence {X : Type*} {Y : Type*}
    (f : X × Y → Set.Icc (0 : ℝ) 1) (δ : ℝ) (hδ : 0 < δ) :
    (∀ (k ℓ : ℕ), 1 ≤ k → 1 ≤ ℓ →
      extractionHeight f δ k 1 = 1 ∧ extractionHeight f δ 1 ℓ = 1) ∧
    (∀ (k ℓ : ℕ), 2 ≤ k → 2 ≤ ℓ →
      extractionHeight f δ (k - 1) ℓ ≠ ⊤ →
      extractionHeight f δ k (ℓ - 1) ≠ ⊤ →
        extractionHeight f δ k ℓ ≠ ⊤ ∧
        extractionHeight f δ k ℓ ≤
          extractionHeight f δ (k - 1) ℓ + extractionHeight f δ k (ℓ - 1) + 1) := by
  refine ⟨fun k ℓ _ _ => ⟨eh_eq_one f δ _ _ (P_one_left f δ hδ k),
    eh_eq_one f δ _ _ (P_one_right f δ hδ ℓ)⟩, ?_⟩
  intro k ℓ hk hℓ h1 h2
  obtain ⟨a, rfl⟩ : ∃ a, k = a + 1 := ⟨k - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, ℓ = b + 1 := ⟨ℓ - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h1 h2 ⊢
  obtain ⟨t1, e1, g1, p1⟩ := eh_ne_top f δ _ _ h1
  obtain ⟨t2, e2, g2, p2⟩ := eh_ne_top f δ _ _ h2
  have hle := eh_le f δ (a + 1) (b + 1) (t1 + t2 + 1) (by omega) (core f δ hδ a b t1 t2 g1 g2 p1 p2)
  refine ⟨ne_top_of_le_ne_top WithTop.coe_ne_top hle, ?_⟩
  rw [e1, e2]
  have : ((t1 + t2 + 1 : ℕ) : WithTop ℕ) = (t1 : WithTop ℕ) + t2 + 1 := by push_cast; rfl
  rwa [this] at hle

end ConantTerry.Orders
end

theorem solution : type_of% @ConantTerry.Orders.chk_extraction_recurrence := @ConantTerry.Orders.chk_extraction_recurrence
