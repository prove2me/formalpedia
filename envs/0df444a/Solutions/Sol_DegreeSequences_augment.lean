-- Prove2me | solution 1 for DegreeSequences.augment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:30:56.177081+00:00
-- url     : https://prove2.me/submissions/e13d2425-765e-491c-b857-0477ba7feab7

module
public import Mathlib
public import Definitions.Def_DegreeSeqLib_DegreeSequences
public import Theorems.Thm_DegreeSequences_degree_editGraph

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open DegreeSequences
namespace DegreeSequences
theorem _root_.solution {V : Type*} [Fintype V] [DecidableEq V] (G' : SimpleGraph V) [DecidableRel G'.Adj]
    (d : V → ℕ) (t p : V) (htp : t ≠ p) (hp1 : 1 ≤ d p)
    (hdeg : ∀ v, G'.degree v + (if v = t then 1 else 0) + (if v = p then 1 else 0) = d v)
    (hQ : d t ≤ #{x | x ≠ t ∧ d p ≤ d x}) :
    ∃ (G : SimpleGraph V) (_ : DecidableRel G.Adj), ∀ v, G.degree v = d v := by
  classical
  by_cases hadj : G'.Adj t p
  · obtain ⟨x, hxt, hpx, htx⟩ : ∃ x, x ≠ t ∧ d p ≤ d x ∧ ¬ G'.Adj t x := by
      by_contra hc
      push Not at hc
      have hsub : ({x | x ≠ t ∧ d p ≤ d x} : Finset V) ⊆ G'.neighborFinset t := by
        intro x hx
        rw [mem_filter] at hx
        exact (mem_neighborFinset _ _ _).mpr (hc x hx.2.1 hx.2.2)
      have h1 := card_le_card hsub
      rw [card_neighborFinset_eq_degree] at h1
      have h2 := hdeg t
      simp only [ite_true, htp, ite_false] at h2
      omega
    have hxp : x ≠ p := fun h => htx (h ▸ hadj)
    have hdx : G'.degree x = d x := by
      have := hdeg x; simp only [hxt, hxp, ite_false] at this; omega
    have hdp : G'.degree p + 1 = d p := by
      have := hdeg p; simp only [htp.symm, ite_false, ite_true] at this; omega
    obtain ⟨y, hxy, hyp, hpy⟩ : ∃ y, G'.Adj x y ∧ y ≠ p ∧ ¬ G'.Adj p y := by
      by_contra hc
      push Not at hc
      have hsub : (G'.neighborFinset x).erase p ⊆ (G'.neighborFinset p).erase t := by
        intro y hy
        simp only [mem_erase, mem_neighborFinset] at hy ⊢
        refine ⟨fun h => htx (h ▸ hy.2).symm, hc y hy.2 hy.1⟩
      have h1 := card_le_card hsub
      have h2 := pred_card_le_card_erase (s := G'.neighborFinset x) (a := p)
      have h3 : t ∈ G'.neighborFinset p := (mem_neighborFinset _ _ _).mpr hadj.symm
      rw [card_erase_of_mem h3, card_neighborFinset_eq_degree] at h1
      rw [card_neighborFinset_eq_degree] at h2
      have h4 : 0 < G'.degree p := by
        rw [← card_neighborFinset_eq_degree]; exact card_pos.mpr ⟨t, h3⟩
      omega
    have hyt : y ≠ t := fun h => htx (h ▸ hxy).symm
    have hxy' : x ≠ y := hxy.ne
    set R : Finset (Sym2 V) := {s(x, y)} with hRdef
    set A : Finset (Sym2 V) := {s(t, x), s(p, y)} with hAdef
    have hR : ∀ e ∈ R, e ∈ G'.edgeSet := by simp [hRdef, hxy]
    have hA : ∀ e ∈ A, e ∉ G'.edgeSet ∧ ¬ e.IsDiag := by
      simp [hAdef, htx, hpy, hxt.symm, hyp.symm]
    refine ⟨editGraph G' R A, inferInstance, fun v => ?_⟩
    have key := degree_editGraph G' R A hR hA v
    have hne : s(t, x) ≠ s(p, y) := by simp [htp, hyt.symm]
    rw [hRdef, hAdef, sum_pair hne, sum_singleton] at key
    rw [hRdef, hAdef]
    simp only [Sym2.mem_iff] at key
    have hv := hdeg v
    by_cases h1 : v = t
    · subst h1; simp [hxt.symm, hyt.symm, htp] at key hv; omega
    by_cases h2 : v = p
    · subst h2; simp [hxp.symm, hyp.symm, h1] at key hv; omega
    by_cases h3 : v = x
    · subst h3; simp [h1, h2, hxy'] at key hv; omega
    by_cases h4 : v = y
    · subst h4; simp [h1, h2, h3] at key hv; omega
    simp [h1, h2, h3, h4] at key hv; omega
  · set A : Finset (Sym2 V) := {s(t, p)} with hAdef
    have hA : ∀ e ∈ A, e ∉ G'.edgeSet ∧ ¬ e.IsDiag := by simp [hAdef, hadj, htp]
    refine ⟨editGraph G' ∅ A, inferInstance, fun v => ?_⟩
    have key := degree_editGraph G' ∅ A (by simp) hA v
    rw [hAdef, sum_singleton, sum_empty] at key
    rw [hAdef]
    simp only [Sym2.mem_iff] at key
    have hv := hdeg v
    by_cases h1 : v = t
    · subst h1; simp [htp] at key hv; omega
    by_cases h2 : v = p
    · subst h2; simp [h1] at key hv; omega
    simp [h1, h2] at key hv; omega
end DegreeSequences
