-- Prove2me | solution 1 for DiscreteConvex.LConvexFunctionsD.qsbw_iff_level_sets_qdl
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T03:42:54.298909+00:00
-- url     : https://prove2.me/submissions/e984dede-b7fa-4c94-bc21-a6343187c3ea

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_QSBw
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_QDL
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_LevelSet

set_option autoImplicit false

open Classical in
open scoped Pointwise in
open DiscreteConvex.LConvexFunctionsD in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (g : (V → ℤ) → WithTop ℝ) :
    QSBw g ↔ ∀ alpha : ℝ, QDL (LevelSet g alpha) := by
  constructor
  · intro h alpha p hp q hq
    simp only [LevelSet, Set.mem_setOf_eq] at hp hq ⊢
    have hpd : p ∈ DomZ g := by
      simp only [DomZ, Set.mem_setOf_eq]
      exact ne_top_of_le_ne_top WithTop.coe_ne_top hp
    have hqd : q ∈ DomZ g := by
      simp only [DomZ, Set.mem_setOf_eq]
      exact ne_top_of_le_ne_top WithTop.coe_ne_top hq
    have h1 := h p hpd q hqd
    have h2 : min (g (p ⊓ q)) (g (p ⊔ q)) ≤ (alpha : WithTop ℝ) :=
      le_trans h1 (max_le hp hq)
    rcases min_le_iff.mp h2 with h3 | h3
    · exact Or.inl h3
    · exact Or.inr h3
  · intro h p hp q hq
    simp only [DomZ, Set.mem_setOf_eq] at hp hq
    obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp hp
    obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.mp hq
    have key := h (max a b) p (by
        simp only [LevelSet, Set.mem_setOf_eq]
        rw [← ha]; exact WithTop.coe_le_coe.mpr (le_max_left a b))
      q (by
        simp only [LevelSet, Set.mem_setOf_eq]
        rw [← hb]; exact WithTop.coe_le_coe.mpr (le_max_right a b))
    simp only [LevelSet, Set.mem_setOf_eq] at key
    have hm : max (g p) (g q) = ((max a b : ℝ) : WithTop ℝ) := by
      rw [← ha, ← hb]; exact (WithTop.coe_max a b).symm
    rw [ge_iff_le, hm]
    rcases key with k | k
    · exact le_trans (min_le_left _ _) k
    · exact le_trans (min_le_right _ _) k
