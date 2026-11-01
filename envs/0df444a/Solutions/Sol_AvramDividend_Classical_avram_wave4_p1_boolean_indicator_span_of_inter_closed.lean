-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_boolean_indicator_span_of_inter_closed
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T19:07:46.130728+00:00
-- url     : https://prove2.me/submissions/26035181-20a0-4207-b29e-65519e04f477

import Mathlib
import Mathlib.MeasureTheory.SetAlgebra

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- For a family of sets containing the universe and closed under binary
intersections, every indicator of its finite Boolean algebra is a *finite*
real linear combination of indicators of the original generators. This
finite-rank normal form is the algebraic bridge from predictable Boolean
rectangle density to elementary predictable marked tensors. -/
theorem solution
    {α : Type*} (G : Set (Set α))
    (hInter : ∀ (s : Set α), s ∈ G → ∀ (t : Set α), t ∈ G → s ∩ t ∈ G)
    (hUniv : (Set.univ : Set α) ∈ G)
    (s : Set α) (hs : s ∈ generateSetAlgebra G) :
    let χ : Set α → (α → ℝ) :=
      fun t => Set.indicator t (fun _ => (1 : ℝ))
    χ s ∈ Submodule.span ℝ
      {v : α → ℝ | ∃ (t : Set α), t ∈ G ∧ χ t = v} := by
  classical
  let χ : Set α → (α → ℝ) :=
    fun t => Set.indicator t (fun _ => (1 : ℝ))
  let S : Set (α → ℝ) :=
    {v | ∃ (t : Set α), t ∈ G ∧ χ t = v}
  let M : Submodule ℝ (α → ℝ) := Submodule.span ℝ S
  change χ s ∈ M
  have hχInter (u v : Set α) : χ (u ∩ v) = χ u * χ v := by
    funext x
    by_cases hu : x ∈ u <;> by_cases hv : x ∈ v <;>
      simp [χ, hu, hv]
  have hχCompl (u : Set α) :
      χ uᶜ = (1 : α → ℝ) - χ u := by
    funext x
    by_cases hu : x ∈ u <;> simp [χ, hu]
  have hχUnion (u v : Set α) :
      χ (u ∪ v) = χ u + χ v - χ (u ∩ v) := by
    funext x
    by_cases hu : x ∈ u <;> by_cases hv : x ∈ v <;>
      simp [χ, hu, hv] <;> ring
  have hOne : (1 : α → ℝ) ∈ M := by
    have h := Submodule.subset_span (R := ℝ) (s := S)
      (show χ (Set.univ : Set α) ∈ S from
        ⟨Set.univ, hUniv, rfl⟩)
    have hχUniv : χ (Set.univ : Set α) = (1 : α → ℝ) := by
      funext x
      simp [χ]
    rw [hχUniv] at h
    exact h
  have hMul : ∀ (f g : α → ℝ), f ∈ M → g ∈ M → f * g ∈ M := by
    intro f g hf hg
    induction hf using Submodule.span_induction with
    | mem u hu =>
      rcases hu with ⟨a, ha, rfl⟩
      induction hg using Submodule.span_induction with
      | mem v hv =>
        rcases hv with ⟨b, hb, rfl⟩
        rw [← hχInter a b]
        exact Submodule.subset_span (R := ℝ) (s := S)
          ⟨a ∩ b, hInter a ha b hb, rfl⟩
      | zero =>
        simp
      | add v w _ _ hv hw =>
        simpa [mul_add] using M.add_mem hv hw
      | smul c v _ hv =>
        have heq : χ a * (c • v) = c • (χ a * v) := by
          funext x
          simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
          ring
        rw [heq]
        exact M.smul_mem c hv
    | zero =>
      simp
    | add u v _ _ hu hv =>
      simpa [add_mul] using M.add_mem hu hv
    | smul c u _ hu =>
      have heq : (c • u) * g = c • (u * g) := by
        funext x
        simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [heq]
      exact M.smul_mem c hu
  induction hs with
  | base u hu =>
    exact Submodule.subset_span (R := ℝ) (s := S)
      ⟨u, hu, rfl⟩
  | empty =>
    have hχEmpty : χ (∅ : Set α) = (0 : α → ℝ) := by
      funext x
      simp [χ]
    rw [hχEmpty]
    exact M.zero_mem
  | compl u hu ih =>
    rw [hχCompl]
    exact M.sub_mem hOne ih
  | union u v hu hv ihu ihv =>
    rw [hχUnion, hχInter]
    exact M.sub_mem (M.add_mem ihu ihv) (hMul (χ u) (χ v) ihu ihv)