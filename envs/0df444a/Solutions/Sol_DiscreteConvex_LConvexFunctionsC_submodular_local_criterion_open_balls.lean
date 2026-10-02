-- Prove2me | solution 1 for DiscreteConvex.LConvexFunctionsC.submodular_local_criterion_open_balls
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T23:05:32.807059+00:00
-- url     : https://prove2.me/submissions/27f51541-aef7-4278-868a-d3fee5d28f99

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_DomR
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_SBFR

set_option autoImplicit false

namespace Cex51c5fc53

open DiscreteConvex.LConvexFunctionsC

/-- The point (1, -1). -/
def a : Fin 2 → ℝ := ![1, -1]
/-- The point (-1, 1). -/
def b : Fin 2 → ℝ := ![-1, 1]

open Classical in
/-- Zero on the two antipodal points `a`, `b`, `⊤` elsewhere. -/
noncomputable def g (p : Fin 2 → ℝ) : WithTop ℝ :=
  if p = a ∨ p = b then 0 else ⊤

theorem g_ne_top {p : Fin 2 → ℝ} : g p ≠ ⊤ ↔ (p = a ∨ p = b) := by
  unfold g
  split_ifs with h
  · simp [h]
  · simp [h]

theorem dom_eq : DomR g = ({a, b} : Set (Fin 2 → ℝ)) := by
  ext p
  simp only [DomR, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  exact g_ne_top

theorem closed : IsClosed (DomR g) := by
  rw [dom_eq]
  exact (Set.toFinite _).isClosed

theorem local_ok : ∀ p0 ∈ DomR g, ∃ eps : ℝ, 0 < eps ∧ ∀ p q : Fin 2 → ℝ,
    (∀ v, |p v - p0 v| ≤ eps) → (∀ v, |q v - p0 v| ≤ eps) →
    g p + g q ≥ g (p ⊔ q) + g (p ⊓ q) := by
  intro p0 hp0
  rw [dom_eq] at hp0
  refine ⟨1, one_pos, fun p q hp hq => ?_⟩
  by_cases hpt : g p = ⊤
  · rw [hpt, WithTop.top_add]; exact le_top
  by_cases hqt : g q = ⊤
  · rw [hqt, WithTop.add_top]; exact le_top
  rw [← ne_eq, g_ne_top] at hpt hqt
  have hpq : p = q := by
    have h1 := hp 0
    have h2 := hq 0
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp0
    rcases hp0 with rfl | rfl <;> rcases hpt with rfl | rfl <;> rcases hqt with rfl | rfl <;>
      first
      | rfl
      | (exfalso
         simp only [a, b, Matrix.cons_val_zero] at h1 h2
         rw [abs_le] at h1 h2
         linarith [h1.1, h1.2, h2.1, h2.2])
  subst hpq
  simp

theorem a_sup_b : a ⊔ b = ![1, 1] := by
  funext i
  fin_cases i <;> simp [a, b]

theorem not_sbfr : ¬ SBFR g := by
  intro h
  have h1 := h a b
  have ha : g a = 0 := by unfold g; simp
  have hb : g b = 0 := by unfold g; simp
  have hab : g (a ⊔ b) = ⊤ := by
    unfold g
    rw [if_neg]
    rw [a_sup_b]
    rintro (h | h)
    · have := congrFun h 1; simp [a] at this; norm_num at this
    · have := congrFun h 0; simp [b] at this; norm_num at this
  rw [ha, hb, hab, WithTop.top_add] at h1
  simp at h1

end Cex51c5fc53

open DiscreteConvex.LConvexFunctionsC in
theorem solution : ¬ (∀ {V : Type} [Fintype V] [DecidableEq V]
    (g : (V → ℝ) → WithTop ℝ), IsClosed (DomR g) →
    (∀ p0 ∈ DomR g, ∃ eps : ℝ, 0 < eps ∧ ∀ p q : V → ℝ,
      (∀ v, |p v - p0 v| ≤ eps) → (∀ v, |q v - p0 v| ≤ eps) →
      g p + g q ≥ g (p ⊔ q) + g (p ⊓ q)) →
    SBFR g) := by
  intro h
  exact Cex51c5fc53.not_sbfr (h Cex51c5fc53.g Cex51c5fc53.closed Cex51c5fc53.local_ok)
