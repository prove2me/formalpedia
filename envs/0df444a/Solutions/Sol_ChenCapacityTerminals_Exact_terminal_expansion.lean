-- Prove2me | solution 1 for ChenCapacityTerminals.Exact.terminal_expansion
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T06:52:00.378924+00:00
-- url     : https://prove2.me/submissions/ff4eed53-5136-48d6-b6a1-3a682b110654
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_ChenCapacityTerminals_Exact_Specifications
import Theorems.Thm_ChenCapacityTerminals_Exact_guide_entries
import Theorems.Thm_ChenCapacityTerminals_Exact_postorder_charging

set_option autoImplicit false
set_option maxHeartbeats 800000

open ChenCapacityTerminals.Exact

theorem solution
    (G : Network) (r d : ℕ) (L : ℚ) (b : ℕ → ℕ) (t : ℕ) (c : Construction)
    (hG : Prepared G r) (hd : 1 ≤ d) (hdn : d ≤ G.vertices.card)
    (hL : 0 < L) (ht : 1 ≤ t) (hc : LegalConstruction G r d L b t c) :
    (RootLowerBound G r L → ∀ X ⊆ G.vertices \
      (c.terminals G r ((L : ℝ) / (4 * d)) b t ∪ {r}),
      (mass b X : ℝ) ≤ (terminalCoefficient G.vertices.card d : ℝ) * t * cut G X / L) ∧
    ((∀ v ∈ G.vertices, b v = 1) → t = d → RootLowerBound G r L →
      ∀ X ⊆ G.vertices \ (c.terminals G r ((L : ℝ) / (4 * d)) b t ∪ {r}),
        (X.card : ℝ) ≤ (terminalCoefficient G.vertices.card d : ℝ) * d * cut G X / L) := by
  classical
  obtain ⟨hsubset, hmarks, hcomponents⟩ := postorder_charging G r d L b t c hc
  have hcoef : (4 : ℝ) * d * (1 + min c.rounds G.vertices.card.log2) ≤
      (terminalCoefficient G.vertices.card d : ℝ) := by
    have hmin : min c.rounds G.vertices.card.log2 ≤ ceilLog₂ G.vertices.card := by
      unfold ceilLog₂
      exact le_trans (min_le_right _ _) (by omega)
    unfold terminalCoefficient
    exact_mod_cast Nat.mul_le_mul_left (4 * d)
      (show 1 + min c.rounds G.vertices.card.log2 ≤ 3 + ceilLog₂ G.vertices.card by omega)
  have hgeneral (hroot : RootLowerBound G r L) (X : Finset ℕ)
      (hX : X ⊆ G.vertices \
        (c.terminals G r ((L : ℝ) / (4 * d)) b t ∪ {r})) :
      (mass b X : ℝ) ≤ (terminalCoefficient G.vertices.card d : ℝ) * t * cut G X / L := by
    have hXearly : X ⊆ G.vertices \ (c.earlyProbes G r ((L : ℝ) / (4 * d)) ∪ {r}) := by
      intro x hx
      have hx' := hX hx
      simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_singleton, not_or] at hx' ⊢
      refine ⟨hx'.1, ?_, hx'.2.2⟩
      intro hxe
      apply hx'.2.1
      unfold Construction.terminals
      exact Finset.mem_union_left _ hxe
    have hX' : X ⊆ G.vertices \
        (c.marks G ((L : ℝ) / (4 * d)) b t ∪ {r}) := by
      intro x hx
      have hx' := hX hx
      simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_singleton, not_or] at hx' ⊢
      refine ⟨hx'.1, ?_, hx'.2.2⟩
      intro hxmarks
      by_cases hxr : x = r
      · exact hx'.2.2 hxr
      by_cases hxd : x = dummy G
      · subst x
        have hle := Finset.le_sup (f := id) hx'.1
        simp only [id_eq] at hle
        unfold dummy at hle
        omega
      apply hx'.2.1
      unfold Construction.terminals
      refine Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hxmarks, ?_⟩)
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hxr, hxd⟩
    have hm := hcomponents X hX'
    have hg := guide_entries G r d L b t c X hG hd hdn hL hroot hc hXearly
    have hLr : (0 : ℝ) < L := by exact_mod_cast hL
    have hdr : (0 : ℝ) < d := by exact_mod_cast (Nat.zero_lt_of_lt hd)
    have hg' : (guideEntries (c.guide G ((L : ℝ) / (4 * d))) X : ℝ) ≤
        cut G X * (4 * (d : ℝ) / L) * (1 + min c.rounds G.vertices.card.log2) := by
      calc
        _ ≤ (1 + min c.rounds G.vertices.card.log2) * cut G X / ((L : ℝ) / (4 * d)) := hg
        _ = cut G X * (4 * (d : ℝ) / L) * (1 + min c.rounds G.vertices.card.log2) := by
          field_simp
          <;> ring
    have hcut : (0 : ℝ) ≤ cut G X := by
      unfold cut weight
      apply List.sum_nonneg
      intro z hz
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hz
      split_ifs
      · exact (hG.1 e he).2.2
      · exact le_rfl
    have htr : (0 : ℝ) ≤ t := by positivity
    have hprod : (t : ℝ) * (cut G X * (4 * (d : ℝ) / L) *
        (1 + min c.rounds G.vertices.card.log2)) ≤
        (terminalCoefficient G.vertices.card d : ℝ) * t * cut G X / L := by
      have hmul := mul_le_mul_of_nonneg_left hcoef (mul_nonneg htr hcut)
      rw [show (t : ℝ) * (cut G X * (4 * (d : ℝ) / L) *
          (1 + min c.rounds G.vertices.card.log2)) =
          (t * cut G X * (4 * (d : ℝ) * (1 + min c.rounds G.vertices.card.log2))) / L by
        field_simp <;> ring]
      rw [show (terminalCoefficient G.vertices.card d : ℝ) * t * cut G X / L =
          (t * cut G X * (terminalCoefficient G.vertices.card d : ℝ)) / L by ring]
      exact div_le_div_of_nonneg_right hmul hLr.le
    exact hm.trans ((mul_le_mul_of_nonneg_left hg' htr).trans hprod)
  constructor
  · exact hgeneral
  · intro hunit htd hroot X hX
    have hmass : mass b X = X.card := by
      unfold mass
      calc
        ∑ u ∈ X, b u = ∑ _u ∈ X, 1 := by
          apply Finset.sum_congr rfl
          intro u hu
          exact hunit u (Finset.mem_sdiff.mp (hX hu)).1
        _ = X.card := by simp
    simpa [htd, hmass] using hgeneral hroot X hX
