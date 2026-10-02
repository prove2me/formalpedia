-- Prove2me | solution 1 for DiscreteConvex.NetworkFlows.cut_capacity_submodular
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T07:00:02.032991+00:00
-- url     : https://prove2.me/submissions/c583a109-b0c2-4044-868a-b48030fa64da

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlows_CutCapacity
import Definitions.Def_DiscreteConvex_NetworkFlows_Submodular

set_option autoImplicit false

namespace Cex73f383db
open DiscreteConvex.NetworkFlows

/-- One arc `0 → 1` with upper capacity `-1` and lower capacity `0` (so `c̄ < c`). -/
theorem cex : ¬ Submodular
    (CutCapacity (V := Fin 2) (A := Unit) (fun _ => 0) (fun _ => 1)
      (fun _ => ((-1 : ℝ) : WithTop ℝ)) (fun _ => ((0 : ℝ) : WithBot ℝ))) := by
  intro h
  have h1 := h {0} {1}
  have e : ({0} : Finset (Fin 2)) ∪ {1} = Finset.univ := by decide
  have e' : ({0} : Finset (Fin 2)) ∩ {1} = ∅ := by decide
  rw [e, e'] at h1
  simp only [CutCapacity, UpperCapOf, NegLowerCapOf, DeltaPlus, DeltaMinus] at h1
  have d1 : (Finset.univ.filter (fun _ : Unit => (0 : Fin 2) ∈ ({0} : Finset (Fin 2)) ∧
      (1 : Fin 2) ∉ ({0} : Finset (Fin 2)))) = Finset.univ := by decide
  have d2 : (Finset.univ.filter (fun _ : Unit => (1 : Fin 2) ∈ ({0} : Finset (Fin 2)) ∧
      (0 : Fin 2) ∉ ({0} : Finset (Fin 2)))) = ∅ := by decide
  have d3 : (Finset.univ.filter (fun _ : Unit => (0 : Fin 2) ∈ ({1} : Finset (Fin 2)) ∧
      (1 : Fin 2) ∉ ({1} : Finset (Fin 2)))) = ∅ := by decide
  have d4 : (Finset.univ.filter (fun _ : Unit => (1 : Fin 2) ∈ ({1} : Finset (Fin 2)) ∧
      (0 : Fin 2) ∉ ({1} : Finset (Fin 2)))) = Finset.univ := by decide
  have d5 : (Finset.univ.filter (fun _ : Unit => (0 : Fin 2) ∈ (Finset.univ : Finset (Fin 2)) ∧
      (1 : Fin 2) ∉ (Finset.univ : Finset (Fin 2)))) = ∅ := by decide
  have d6 : (Finset.univ.filter (fun _ : Unit => (1 : Fin 2) ∈ (Finset.univ : Finset (Fin 2)) ∧
      (0 : Fin 2) ∉ (Finset.univ : Finset (Fin 2)))) = ∅ := by decide
  have d7 : (Finset.univ.filter (fun _ : Unit => (0 : Fin 2) ∈ (∅ : Finset (Fin 2)) ∧
      (1 : Fin 2) ∉ (∅ : Finset (Fin 2)))) = ∅ := by decide
  have d8 : (Finset.univ.filter (fun _ : Unit => (1 : Fin 2) ∈ (∅ : Finset (Fin 2)) ∧
      (0 : Fin 2) ∉ (∅ : Finset (Fin 2)))) = ∅ := by decide
  rw [d1, d2, d3, d4, d5, d6, d7, d8] at h1
  have h0 : NegLowerToUpper ((0 : ℝ) : WithBot ℝ) = 0 := by
    show (((-0 : ℝ)) : WithTop ℝ) = 0
    simp
  simp only [Finset.sum_empty, Finset.univ_unique, Finset.sum_singleton, h0,
    add_zero, zero_add] at h1
  have : ((-1 : ℝ) : WithTop ℝ) < 0 := by
    exact_mod_cast (by norm_num : (-1 : ℝ) < 0)
  exact absurd h1 (not_le.mpr this)

end Cex73f383db

theorem solution : ¬ (∀ {V A : Type} [Fintype V] [Fintype A] [DecidableEq V]
    (tail head : A → V) (cUpper : A → WithTop ℝ) (cLower : A → WithBot ℝ),
    DiscreteConvex.NetworkFlows.Submodular
      (DiscreteConvex.NetworkFlows.CutCapacity tail head cUpper cLower)) := by
  intro h
  exact Cex73f383db.cex (h _ _ _ _)
