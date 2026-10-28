-- Prove2me | solution 1 for DiscreteConvex.LConvexFunctionsC.sbf_nat_r_iff_polyhedral_lnat_convex
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T16:08:48.740968+00:00
-- url     : https://prove2.me/submissions/9f19b20d-72e2-4f7d-9b54-1d57fede77d8

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_DomR
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_SBFNatR
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_LNaturalConvexR

open DiscreteConvex.LConvexFunctionsC

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (g : (V → ℝ) → WithTop ℝ) (hdom : (DomR g).Nonempty) :
    SBFNatR g ↔ LNaturalConvexR g := by
  constructor
  · intro h
    refine ⟨?_, ⟨0, ?_⟩⟩
    · intro X Y
      simp only [LiftedFunctionLR, Pi.sup_apply, Pi.inf_apply]
      rcases le_total (Y none) (X none) with hle | hle
      · have := h (fun v => Y (some v) - Y none) (fun v => X (some v) - X none)
          (X none - Y none) (by linarith)
        have e1 : (fun v => max (Y (some v) - Y none - (X none - Y none)) (X (some v) - X none))
            = (fun v => max (X (some v)) (Y (some v)) - max (X none) (Y none)) := by
          funext v; rw [max_eq_left hle, ← max_sub_sub_right, max_comm (X (some v) - X none)]; congr 1 <;> ring
        have e2 : (fun v => min (Y (some v) - Y none) (X (some v) - X none + (X none - Y none)))
            = (fun v => min (X (some v)) (Y (some v)) - min (X none) (Y none)) := by
          funext v; rw [min_eq_right hle, ← min_sub_sub_right, min_comm (X (some v) - Y none)]; congr 1 <;> ring
        rw [e1, e2, add_comm (g _)] at this
        exact this
      · have := h (fun v => X (some v) - X none) (fun v => Y (some v) - Y none)
          (Y none - X none) (by linarith)
        have e1 : (fun v => max (X (some v) - X none - (Y none - X none)) (Y (some v) - Y none))
            = (fun v => max (X (some v)) (Y (some v)) - max (X none) (Y none)) := by
          funext v; rw [max_eq_right hle, ← max_sub_sub_right]; congr 1 <;> ring
        have e2 : (fun v => min (X (some v) - X none) (Y (some v) - Y none + (Y none - X none)))
            = (fun v => min (X (some v)) (Y (some v)) - min (X none) (Y none)) := by
          funext v; rw [min_eq_left hle, ← min_sub_sub_right]; congr 1 <;> ring
        rw [e1, e2] at this
        exact this
    · intro p alpha
      simp only [LiftedFunctionLR, mul_zero, WithTop.coe_zero, add_zero]
      congr 1; funext v; ring
  · rintro ⟨h, -⟩ p q alpha halpha
    have := h (fun o => Option.elim o 0 p) (fun o => Option.elim o alpha (fun v => q v + alpha))
    simp only [LiftedFunctionLR, Pi.sup_apply, Pi.inf_apply, Option.elim] at this
    have e0 : (fun v => q v + alpha - alpha) = q := by funext v; ring
    have e1 : (fun v => max (p v) (q v + alpha) - max 0 alpha) = (fun v => max (p v - alpha) (q v)) := by
      funext v; rw [max_eq_right halpha, ← max_sub_sub_right]; congr 1 <;> ring
    have e2 : (fun v => min (p v) (q v + alpha) - min 0 alpha) = (fun v => min (p v) (q v + alpha)) := by
      funext v; rw [min_eq_left halpha]; ring
    have e3 : (fun v => p v - 0) = p := by funext v; ring
    rw [e0, e1, e2, e3] at this
    exact this
