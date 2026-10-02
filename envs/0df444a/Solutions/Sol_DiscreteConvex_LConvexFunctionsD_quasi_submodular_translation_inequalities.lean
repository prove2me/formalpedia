-- Prove2me | solution 1 for DiscreteConvex.LConvexFunctionsD.quasi_submodular_translation_inequalities
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T04:24:10.024974+00:00
-- url     : https://prove2.me/submissions/f070b242-4bd8-460b-b731-164feaa77ae2

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_SSQSB
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_QSBw
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_SSQSBw

set_option autoImplicit false

namespace Cex94b7f3ef

open DiscreteConvex.LConvexFunctionsD

/-- `0` on the diagonal `p 0 = p 1`, `+∞` elsewhere. -/
noncomputable def g : (Fin 2 → ℤ) → WithTop ℝ :=
  fun p => if p 0 = p 1 then (0 : WithTop ℝ) else ⊤

theorem hper : ∀ p : Fin 2 → ℤ, g (p + 1) = g p := by
  intro p
  simp [g]

open Classical in
theorem hss : SSQSBw g := by
  intro p hp q hq
  have hp' : p 0 = p 1 := by
    by_contra h
    exact hp (by simp [g, h])
  have hq' : q 0 = q 1 := by
    by_contra h
    exact hq (by simp [g, h])
  right
  simp [g, hp', hq']

end Cex94b7f3ef

open Classical in
open scoped Pointwise in
theorem solution : ¬ (∀ {V : Type} [Fintype V] [DecidableEq V]
    (g : (V → ℤ) → WithTop ℝ)
    (hper : ∀ p : V → ℤ, g (p + 1) = g p),
    (DiscreteConvex.LConvexFunctionsD.QSBw g → ∀ p q : V → ℤ, ∀ alpha : ℤ,
        max (g p) (g q) ≥
          min (g (fun v => max (p v) (q v - alpha))) (g (fun v => min (p v + alpha) (q v)))) ∧
    (DiscreteConvex.LConvexFunctionsD.SSQSBw g → ∀ p q : V → ℤ, g p ≠ g q → ∀ alpha : ℤ,
        max (g p) (g q) >
          min (g (fun v => max (p v) (q v - alpha))) (g (fun v => min (p v + alpha) (q v)))) ∧
    (DiscreteConvex.LConvexFunctionsD.SSQSB g → ∀ p q : V → ℤ, ∀ alpha : ℤ,
        (g (fun v => max (p v) (q v - alpha)) ≥ g p →
          g (fun v => min (p v + alpha) (q v)) ≤ g q) ∧
        (g (fun v => min (p v + alpha) (q v)) ≥ g q →
          g (fun v => max (p v) (q v - alpha)) ≤ g p))) := by
  intro h
  have h2 := (h (V := Fin 2) Cex94b7f3ef.g Cex94b7f3ef.hper).2.1 Cex94b7f3ef.hss
    ![2, 0] ![0, 0] (by simp [Cex94b7f3ef.g]) (-1)
  simp [Cex94b7f3ef.g] at h2
