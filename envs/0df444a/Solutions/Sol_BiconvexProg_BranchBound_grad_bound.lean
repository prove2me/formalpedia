-- Prove2me | solution 1 for BiconvexProg.BranchBound.grad_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:53:50.962976+00:00
-- url     : https://prove2.me/submissions/ebf64b43-c403-4bbd-81e9-3173dc9bf34a

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_gradNormMax

namespace BiconvexProg.BranchBound

lemma aux_gb_sq (l L x : ℝ) (h1 : l ≤ x) (h2 : x ≤ L) : x ^ 2 ≤ max (l ^ 2) (L ^ 2) := by
  rcases le_total 0 x with hx | hx
  · exact le_max_of_le_right (by nlinarith)
  · exact le_max_of_le_left (by nlinarith)

lemma aux_gb_corner (l L : ℝ) : ∃ α ∈ ({l, L} : Set ℝ), α ^ 2 = max (l ^ 2) (L ^ 2) := by
  rcases le_total (l ^ 2) (L ^ 2) with h | h
  · exact ⟨L, by simp, (max_eq_right h).symm⟩
  · exact ⟨l, by simp, (max_eq_left h).symm⟩

lemma aux_gb_mem (l L α : ℝ) (hlL : l ≤ L) (h : α ∈ ({l, L} : Set ℝ)) : α ∈ Set.Icc l L := by
  rcases h with h | h
  · subst h; exact ⟨le_rfl, hlL⟩
  · rw [Set.mem_singleton_iff] at h; subst h; exact ⟨hlL, le_rfl⟩

lemma aux_gb_greatest (l L m M : ℝ) (hlL : l ≤ L) (hmM : m ≤ M) :
    ∃ α ∈ ({l, L} : Set ℝ), ∃ β ∈ ({m, M} : Set ℝ),
      IsGreatest ((fun p : ℝ × ℝ => Real.sqrt (p.2 ^ 2 + p.1 ^ 2)) '' (Set.Icc l L ×ˢ Set.Icc m M))
        (Real.sqrt (β ^ 2 + α ^ 2)) := by
  obtain ⟨α, hα, hαe⟩ := aux_gb_corner l L
  obtain ⟨β, hβ, hβe⟩ := aux_gb_corner m M
  refine ⟨α, hα, β, hβ, ⟨⟨(α, β), ⟨aux_gb_mem l L α hlL hα, aux_gb_mem m M β hmM hβ⟩, rfl⟩, ?_⟩⟩
  rintro _ ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
  apply Real.sqrt_le_sqrt
  have h1 := aux_gb_sq l L x hx.1 hx.2
  have h2 := aux_gb_sq m M y hy.1 hy.2
  simp only
  linarith

end BiconvexProg.BranchBound

open BiconvexProg.BranchBound

theorem solution (l L m M : ℝ) (hlL : l ≤ L) (hmM : m ≤ M) :
    (∃ α ∈ ({l, L} : Set ℝ), ∃ β ∈ ({m, M} : Set ℝ),
      gradNormMax l L m M = Real.sqrt (β ^ 2 + α ^ 2)) ∧
    ∀ l' L' m' M' : ℝ, l ≤ l' → l' ≤ L' → L' ≤ L → m ≤ m' → m' ≤ M' → M' ≤ M →
      Real.sqrt (m' ^ 2 + l' ^ 2) ≤ gradNormMax l L m M ∧
        Real.sqrt (M' ^ 2 + L' ^ 2) ≤ gradNormMax l L m M := by
  obtain ⟨α, hα, β, hβ, hG⟩ := aux_gb_greatest l L m M hlL hmM
  have hEq : gradNormMax l L m M = Real.sqrt (β ^ 2 + α ^ 2) := hG.csSup_eq
  refine ⟨⟨α, hα, β, hβ, hEq⟩, ?_⟩
  intro l' L' m' M' h1 h2 h3 h4 h5 h6
  rw [hEq]
  constructor
  · exact hG.2 ⟨(l', m'), ⟨⟨h1, h2.trans h3⟩, ⟨h4, h5.trans h6⟩⟩, rfl⟩
  · exact hG.2 ⟨(L', M'), ⟨⟨h1.trans h2, h3⟩, ⟨h4.trans h5, h6⟩⟩, rfl⟩
