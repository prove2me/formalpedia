-- Prove2me | solution 1 for DiscreteConvex.LConvexSetsB.induced_gamma_recovers_lconvex
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T05:18:29.847685+00:00
-- url     : https://prove2.me/submissions/0581f838-05f8-458e-b566-99050de5cd7c

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexSetsB_DistanceFunction
import Definitions.Def_DiscreteConvex_LConvexSetsB_IsIntegerValuedGamma
import Definitions.Def_DiscreteConvex_LConvexSetsB_AdmissiblePotentials
import Definitions.Def_DiscreteConvex_LConvexSetsB_LConvexSet

set_option autoImplicit false

open DiscreteConvex.LConvexSetsB in
theorem ee6957ae_mono {g : WithTop ℝ} {x y : ℝ} (hxy : x ≤ y)
    (hy : ((y : ℝ) : WithTop ℝ) ≤ g) : ((x : ℝ) : WithTop ℝ) ≤ g :=
  le_trans (WithTop.coe_le_coe.mpr hxy) hy

open DiscreteConvex.LConvexSetsB in
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (γ : V → V → WithTop ℝ) (hγ : DistanceFunction γ) (hInt : IsIntegerValuedGamma γ)
    (hne : (AdmissiblePotentials γ).Nonempty) :
    LConvexSet {p : V → ℤ | (fun v => (p v : ℝ)) ∈ AdmissiblePotentials γ} := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨p, hp⟩ := hne
    refine ⟨fun v => ⌊p v⌋, ?_⟩
    intro u v huv
    have h := hp u v huv
    rcases hInt u v with htop | ⟨k, hk⟩
    · rw [htop]; exact le_top
    · rw [hk] at h ⊢
      have h' : p v - p u ≤ (k : ℝ) := WithTop.coe_le_coe.mp h
      apply WithTop.coe_le_coe.mpr
      have h1 : ⌊p v⌋ ≤ ⌊p u + (k : ℝ)⌋ := Int.floor_mono (by linarith)
      rw [Int.floor_add_intCast] at h1
      have h2 : ((⌊p v⌋ : ℤ) : ℝ) ≤ ((⌊p u⌋ + k : ℤ) : ℝ) := by exact_mod_cast h1
      push_cast at h2
      linarith
  · intro p hp q hq
    refine ⟨?_, ?_⟩
    · intro u v huv
      have hpu := hp u v huv
      have hqu := hq u v huv
      simp only [Set.mem_setOf_eq] at hpu hqu ⊢
      rcases le_total (p v) (q v) with h | h
      · rw [max_eq_right h]
        apply ee6957ae_mono _ hqu
        have : (q u : ℝ) ≤ ((max (p u) (q u) : ℤ) : ℝ) := by exact_mod_cast le_max_right _ _
        linarith
      · rw [max_eq_left h]
        apply ee6957ae_mono _ hpu
        have : (p u : ℝ) ≤ ((max (p u) (q u) : ℤ) : ℝ) := by exact_mod_cast le_max_left _ _
        linarith
    · intro u v huv
      have hpu := hp u v huv
      have hqu := hq u v huv
      simp only [Set.mem_setOf_eq] at hpu hqu ⊢
      rcases le_total (p u) (q u) with h | h
      · rw [min_eq_left h]
        apply ee6957ae_mono _ hpu
        have : ((min (p v) (q v) : ℤ) : ℝ) ≤ (p v : ℝ) := by exact_mod_cast min_le_left _ _
        linarith
      · rw [min_eq_right h]
        apply ee6957ae_mono _ hqu
        have : ((min (p v) (q v) : ℤ) : ℝ) ≤ (q v : ℝ) := by exact_mod_cast min_le_right _ _
        linarith
  · intro p hp
    refine ⟨?_, ?_⟩
    · intro u v huv
      have hpu := hp u v huv
      simp only [Set.mem_setOf_eq] at hpu ⊢
      apply ee6957ae_mono _ hpu
      push_cast
      linarith
    · intro u v huv
      have hpu := hp u v huv
      simp only [Set.mem_setOf_eq] at hpu ⊢
      apply ee6957ae_mono _ hpu
      push_cast
      linarith
