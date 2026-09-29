-- Prove2me | solution 1 for FinitelyAdditive.exists_extension_of_isSetRing
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-23T16:04:57.926534+00:00
-- url     : https://prove2.me/submissions/439e8823-6397-4fee-933c-3811910c28c0

import Mathlib

/-!
# A finitely additive measure on a ring of sets extends to all subsets

The space `Set X → ℝ≥0∞` is compact, and for each finite family of sets in `R` the conditions
"finitely additive on all subsets, equal to `μ` on the family" cut out a nonempty closed set, so
the whole intersection is nonempty. Nonemptiness is an induction on the family: split the union
`A` of the family along each new set `B` into `A ∩ B` and `A \ B`, and at the bottom put the mass
`μ A` on a single point of `A`.
-/

open MeasureTheory Set Topology
open scoped ENNReal

namespace FinitelyAdditive.Lib

variable {X : Type*}

/-- Finite additivity on all subsets. -/
def FA (ν : Set X → ℝ≥0∞) : Prop :=
  ν ∅ = 0 ∧ ∀ s t : Set X, Disjoint s t → ν (s ∪ t) = ν s + ν t

theorem fa_add {ν₁ ν₂ : Set X → ℝ≥0∞} (h₁ : FA ν₁) (h₂ : FA ν₂) : FA (ν₁ + ν₂) := by
  refine ⟨by simp [h₁.1, h₂.1], fun s t hst => ?_⟩
  simp only [Pi.add_apply, h₁.2 s t hst, h₂.2 s t hst]
  ring

open Classical in
theorem fa_dirac (x : X) (c : ℝ≥0∞) : FA (fun S => if x ∈ S then c else 0) := by
  refine ⟨by simp, fun s t hst => ?_⟩
  by_cases hs : x ∈ s
  · have ht : x ∉ t := fun ht => Set.disjoint_left.1 hst hs ht
    simp [hs, ht]
  · by_cases ht : x ∈ t <;> simp [hs, ht]

variable {R : Set (Set X)} (hR : IsSetRing R) (μ : Set X → ℝ≥0∞) (h0 : μ ∅ = 0)
  (hadd : ∀ s ∈ R, ∀ t ∈ R, Disjoint s t → μ (s ∪ t) = μ s + μ t)
include hR h0 hadd

omit h0 hadd in
theorem inter_mem {A B : Set X} (hA : A ∈ R) (hB : B ∈ R) : A ∩ B ∈ R := by
  have : A ∩ B = A \ (A \ B) := by ext y; simp only [mem_inter_iff, mem_sdiff, mem_union, mem_empty_iff_false, iff_false]; tauto
  rw [this]; exact hR.sdiff_mem hA (hR.sdiff_mem hA hB)

/-- The finite step: a finitely additive `ν` living inside `A`, matching `μ (A ∩ C)` on each `C`
of the list. -/
theorem exists_local (L : List (Set X)) (hL : ∀ C ∈ L, C ∈ R) :
    ∀ A ∈ R, ∃ ν : Set X → ℝ≥0∞, FA ν ∧ (∀ S, ν S = ν (S ∩ A)) ∧ ν A = μ A ∧
      ∀ C ∈ L, ν C = μ (A ∩ C) := by
  classical
  induction L with
  | nil =>
    intro A hA
    rcases A.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · exact ⟨fun _ => 0, ⟨rfl, fun _ _ _ => by simp⟩, fun _ => rfl, h0.symm, by simp⟩
    · refine ⟨fun S => if x ∈ S then μ A else 0, fa_dirac x _, fun S => ?_, by simp [hx], by simp⟩
      simp [hx]
  | cons B L ih =>
    intro A hA
    have hB : B ∈ R := hL B (by simp)
    have hL' : ∀ C ∈ L, C ∈ R := fun C hC => hL C (by simp [hC])
    have hAB : A ∩ B ∈ R := inter_mem hR hA hB
    have hAmB : A \ B ∈ R := hR.sdiff_mem hA hB
    obtain ⟨ν₁, f₁, s₁, a₁, c₁⟩ := ih hL' _ hAB
    obtain ⟨ν₂, f₂, s₂, a₂, c₂⟩ := ih hL' _ hAmB
    have split : ∀ D ∈ R, μ (A ∩ D) = μ (A ∩ B ∩ D) + μ (A \ B ∩ D) := by
      intro D hD
      rw [← hadd _ (inter_mem hR hAB hD) _ (inter_mem hR hAmB hD)]
      · congr 1; ext y; simp only [mem_inter_iff, mem_sdiff, mem_union, mem_empty_iff_false, iff_false]; tauto
      · exact Set.disjoint_left.2 fun y h1 h2 => h2.1.2 h1.1.2
    refine ⟨ν₁ + ν₂, fa_add f₁ f₂, fun S => ?_, ?_, ?_⟩
    · simp only [Pi.add_apply]
      rw [s₁ S, s₁ (S ∩ A), s₂ S, s₂ (S ∩ A)]
      congr 2 <;> ext <;> simp <;> tauto
    · simp only [Pi.add_apply]
      have e1 : A ∩ (A ∩ B) = A ∩ B := by
        ext y; simp only [mem_inter_iff, mem_sdiff, mem_union, mem_empty_iff_false, iff_false]; tauto
      have e2 : A ∩ (A \ B) = A \ B := by
        ext y; simp only [mem_inter_iff, mem_sdiff, mem_union, mem_empty_iff_false, iff_false]; tauto
      rw [s₁ A, s₂ A, e1, e2, a₁, a₂,
        ← hadd _ hAB _ hAmB (Set.disjoint_left.2 fun y h1 h2 => h2.2 h1.2)]
      congr 1; ext y; simp only [mem_inter_iff, mem_sdiff, mem_union, mem_empty_iff_false, iff_false]; tauto
    · intro C hC
      simp only [List.mem_cons] at hC
      rcases hC with rfl | hC
      · simp only [Pi.add_apply]
        rw [s₁, s₂, congrArg ν₁ (by ext y; simp only [mem_inter_iff, mem_sdiff, mem_union, mem_empty_iff_false, iff_false]; tauto : C ∩ (A ∩ C) = A ∩ C), a₁,
          congrArg ν₂ (by ext y; simp only [mem_inter_iff, mem_sdiff, mem_union, mem_empty_iff_false, iff_false]; tauto : C ∩ (A \ C) = ∅), f₂.1, add_zero]
      · simp only [Pi.add_apply]
        rw [c₁ C hC, c₂ C hC, split C (hL' C hC)]

end FinitelyAdditive.Lib

namespace FinitelyAdditive

open Lib in
theorem exists_extension_of_isSetRing_aux {X : Type*} {R : Set (Set X)} (hR : IsSetRing R)
    (μ : Set X → ℝ≥0∞) (h0 : μ ∅ = 0)
    (hadd : ∀ s ∈ R, ∀ t ∈ R, Disjoint s t → μ (s ∪ t) = μ s + μ t) :
    ∃ ν : Set X → ℝ≥0∞, ν ∅ = 0 ∧ (∀ s t : Set X, Disjoint s t → ν (s ∪ t) = ν s + ν t) ∧
      ∀ s ∈ R, ν s = μ s := by
  classical
  let T : Finset (Set X) → Set (Set X → ℝ≥0∞) :=
    fun F => {ν | FA ν ∧ ∀ B ∈ F, B ∈ R → ν B = μ B}
  have hcl : ∀ F, IsClosed (T F) := by
    intro F
    have hfa : IsClosed {ν : Set X → ℝ≥0∞ | FA ν} := by
      have : {ν : Set X → ℝ≥0∞ | FA ν} = {ν | ν ∅ = 0} ∩
          ⋂ p : {p : Set X × Set X // Disjoint p.1 p.2},
            {ν | ν (p.1.1 ∪ p.1.2) = ν p.1.1 + ν p.1.2} := by
        ext ν; simp only [FA, mem_ofPred_eq, mem_inter_iff, mem_iInter, Subtype.forall, Prod.forall]
      rw [this]
      refine (isClosed_eq (continuous_apply _) continuous_const).inter
        (isClosed_iInter fun p => isClosed_eq (continuous_apply _) ?_)
      exact (continuous_apply _).add (continuous_apply _)
    have : T F = {ν | FA ν} ∩ ⋂ B ∈ F, ⋂ (_ : B ∈ R), {ν | ν B = μ B} := by
      ext ν; simp [T]
    rw [this]
    exact hfa.inter (isClosed_biInter fun B _ =>
      isClosed_iInter fun _ => isClosed_eq (continuous_apply _) continuous_const)
  have hne : ∀ F, (T F).Nonempty := by
    intro F
    let L := (F.filter (· ∈ R)).toList
    have hL : ∀ C ∈ L, C ∈ R := fun C hC => by simpa [L] using (Finset.mem_filter.1 (by simpa [L] using hC)).2
    let A := L.foldr (· ∪ ·) ∅
    have hAR : ∀ M : List (Set X), (∀ C ∈ M, C ∈ R) → M.foldr (· ∪ ·) ∅ ∈ R := by
      intro M hM
      induction M with
      | nil => exact hR.empty_mem
      | cons C M ih =>
        exact hR.union_mem (hM C (by simp)) (ih fun D hD => hM D (by simp [hD]))
    have hsub : ∀ M : List (Set X), ∀ C ∈ M, C ⊆ M.foldr (· ∪ ·) ∅ := by
      intro M
      induction M with
      | nil => simp
      | cons D M ih =>
        intro C hC
        simp only [List.mem_cons] at hC
        rcases hC with rfl | hC
        · exact subset_union_left
        · exact (ih C hC).trans subset_union_right
    obtain ⟨ν, hf, -, -, hc⟩ := exists_local hR μ h0 hadd L hL A (hAR L hL)
    refine ⟨ν, hf, fun B hB hBR => ?_⟩
    have hBL : B ∈ L := by simp [L, hB, hBR]
    rw [hc B hBL, inter_eq_right.2 (hsub L B hBL)]
  have hdir : Directed (· ⊇ ·) T := by
    intro F G
    refine ⟨F ∪ G, fun ν hν => ⟨hν.1, fun B hB => hν.2 B (by simp [hB])⟩,
      fun ν hν => ⟨hν.1, fun B hB => hν.2 B (by simp [hB])⟩⟩
  obtain ⟨ν, hν⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed T hdir hne
    (fun F => (hcl F).isCompact) hcl
  simp only [mem_iInter] at hν
  refine ⟨ν, (hν ∅).1.1, (hν ∅).1.2, fun s hs => (hν {s}).2 s (by simp) hs⟩

end FinitelyAdditive


open MeasureTheory
open scoped ENNReal

theorem solution {X : Type*} {R : Set (Set X)} (hR : IsSetRing R)
    (μ : Set X → ℝ≥0∞) (h0 : μ ∅ = 0)
    (hadd : ∀ s ∈ R, ∀ t ∈ R, Disjoint s t → μ (s ∪ t) = μ s + μ t) :
    ∃ ν : Set X → ℝ≥0∞, ν ∅ = 0 ∧ (∀ s t : Set X, Disjoint s t → ν (s ∪ t) = ν s + ν t) ∧
      ∀ s ∈ R, ν s = μ s :=
  FinitelyAdditive.exists_extension_of_isSetRing_aux hR μ h0 hadd
