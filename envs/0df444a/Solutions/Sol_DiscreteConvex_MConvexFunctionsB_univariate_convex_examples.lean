-- Prove2me | solution 1 for DiscreteConvex.MConvexFunctionsB.univariate_convex_examples
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:43:05.339528+00:00
-- url     : https://prove2.me/submissions/5cc0973a-06c8-4504-aead-5eaf65d95c17

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_DiscreteConvexUnivariate
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_MNaturalConvex
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_UnivToFunc
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_ConservationLift
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_QuasiSeparable

set_option autoImplicit false
set_option linter.unusedVariables false

open DiscreteConvex.MConvexFunctionsB

namespace UnivCex

/-- `ψ = 0` on `{0, 3}` and `+∞` elsewhere: midpoint convex, but with a hole in its domain. -/
noncomputable def psi (x : ℤ) : WithTop ℝ :=
  if x = 0 ∨ x = 3 then ((0 : ℝ) : WithTop ℝ) else ⊤

theorem psi_dcu : DiscreteConvexUnivariate psi := by
  refine ⟨⟨0, by simp [psi]⟩, fun x => ?_⟩
  by_cases h1 : x = 0 ∨ x = 3
  · by_cases h2 : x + 2 = 0 ∨ x + 2 = 3
    · exfalso; omega
    · have : psi (x + 2) = ⊤ := by simp only [psi]; rw [if_neg h2]
      rw [this]; simp
  · have : psi x = ⊤ := by simp only [psi]; rw [if_neg h1]
    rw [this]; simp

theorem not_mnat : ¬ MNaturalConvex (UnivToFunc psi) := by
  intro h
  let x : Option Unit → ℤ := fun w => w.elim (-3) (fun _ => 3)
  let y : Option Unit → ℤ := fun _ => 0
  have hx : x ∈ DomZ (LiftedFunction (UnivToFunc psi)) := by
    simp [DomZ, LiftedFunction, UnivToFunc, psi, x]
  have hy : y ∈ DomZ (LiftedFunction (UnivToFunc psi)) := by
    simp [DomZ, LiftedFunction, UnivToFunc, psi, y]
  obtain ⟨v, hv, hineq⟩ := h x hx y hy (some ()) (by simp [SuppPos, x, y])
  cases v with
  | some u => simp [SuppNeg, x, y] at hv
  | none =>
    have hl : LiftedFunction (UnivToFunc psi)
        (fun w => x w - CharVec (some ()) w + CharVec none w) = ⊤ := by
      simp [LiftedFunction, UnivToFunc, psi, x, CharVec]
    have h0 : LiftedFunction (UnivToFunc psi) x + LiftedFunction (UnivToFunc psi) y =
        ((0 : ℝ) : WithTop ℝ) := by
      simp [LiftedFunction, UnivToFunc, psi, x, y]
    rw [hl, h0, top_add] at hineq
    exact WithTop.coe_ne_top (top_le_iff.mp hineq)

end UnivCex

theorem solution : ¬ (∀ (psi : ℤ → WithTop ℝ) (hpsi : DiscreteConvexUnivariate psi),
    MNaturalConvex (UnivToFunc psi) ∧
    MExchangeAxiom (ConservationLift psi) ∧
    (∀ {W : Type} [Fintype W] [DecidableEq W] (f0 : ℤ → WithTop ℝ) (fi : W → ℤ → WithTop ℝ),
      DiscreteConvexUnivariate f0 → (∀ v, DiscreteConvexUnivariate (fi v)) →
      MNaturalConvex (QuasiSeparable f0 fi))) := by
  intro h
  exact UnivCex.not_mnat (h UnivCex.psi UnivCex.psi_dcu).1

#print axioms solution
