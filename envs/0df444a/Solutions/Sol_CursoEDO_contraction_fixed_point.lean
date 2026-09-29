-- Prove2me | solution 1 for CursoEDO.contraction_fixed_point
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-19T14:07:32.619113+00:00
-- url     : https://prove2.me/submissions/d581d0cd-75a6-4c3e-8830-b1bf77bbca9f

import Mathlib

theorem solution {X : Type*} [MetricSpace X] [CompleteSpace X] [Nonempty X]
    (F : X → X) (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    (hF : ∀ x y : X, dist (F x) (F y) ≤ lam * dist x y) :
    ∃ p : X, F p = p ∧ (∀ q : X, F q = q → q = p) ∧
      ∀ x : X, Filter.Tendsto (fun n : ℕ => F^[n] x) Filter.atTop (nhds p) := by
  have hlip : LipschitzWith ⟨lam, hlam0⟩ F :=
    LipschitzWith.of_dist_le_mul (fun x y => hF x y)
  have hlt : (⟨lam, hlam0⟩ : NNReal) < 1 := by
    exact hlam1
  have hc : ContractingWith ⟨lam, hlam0⟩ F := ⟨hlt, hlip⟩
  refine ⟨hc.fixedPoint F, hc.fixedPoint_isFixedPt, fun q hq => hc.fixedPoint_unique hq,
    fun x => hc.tendsto_iterate_fixedPoint x⟩
