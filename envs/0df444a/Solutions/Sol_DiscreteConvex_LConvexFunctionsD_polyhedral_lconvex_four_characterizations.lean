-- Prove2me | solution 1 for DiscreteConvex.LConvexFunctionsD.polyhedral_lconvex_four_characterizations
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:36:38.89917+00:00
-- url     : https://prove2.me/submissions/a4d60579-316c-4ddc-a700-0a8489f3fb0a

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_DomR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_SBFR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_TRFR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_ZeroLR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_LinearWeightR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_ArgMinR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_MConvexPolyhedronR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_LConvexPolyhedronR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_DirDeriv
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_SubDifferentialR

set_option autoImplicit false
set_option linter.unusedVariables false

open DiscreteConvex.LConvexFunctionsD

namespace SqCex

/-- `g(p) = p²` on `ℝ^Unit`. -/
def g (p : Unit → ℝ) : WithTop ℝ := (((p ()) ^ 2 : ℝ) : WithTop ℝ)

theorem subdiff (p : Unit → ℝ) : SubDifferentialR g p = {fun _ => 2 * p ()} := by
  ext x
  simp only [SubDifferentialR, Set.mem_ofPred_eq, Set.mem_singleton_iff, g]
  have key : ∀ q : Unit → ℝ, ((((q ()) ^ 2 : ℝ) : WithTop ℝ) - (((p ()) ^ 2 : ℝ) : WithTop ℝ) ≥
      (((∑ v, x v * (q v - p v)) : ℝ) : WithTop ℝ)) ↔
      x () * (q () - p ()) ≤ q () ^ 2 - p () ^ 2 := by
    intro q
    rw [show (((q ()) ^ 2 : ℝ) : WithTop ℝ) - (((p ()) ^ 2 : ℝ) : WithTop ℝ) =
      (((q ()) ^ 2 - (p ()) ^ 2 : ℝ) : WithTop ℝ) by norm_cast]
    simp only [Finset.univ_unique, Finset.sum_singleton, ge_iff_le, WithTop.coe_le_coe]
  simp only [key]
  constructor
  · intro h
    have h1 := h (fun _ => p () + (x () - 2 * p ()) / 2)
    funext u
    cases u
    nlinarith [sq_nonneg (x () - 2 * p ())]
  · rintro rfl q
    nlinarith [sq_nonneg (q () - p ())]

theorem c_holds : ∀ p ∈ DomR g, MConvexPolyhedronR (SubDifferentialR g p) := by
  intro p _
  rw [subdiff]
  refine ⟨⟨2, fun i _ => if i = 0 then 1 else -1, fun i => if i = 0 then 2 * p () else -(2 * p ()),
    ?_⟩, ?_⟩
  · ext x
    simp only [Set.mem_singleton_iff, Set.mem_ofPred_eq, Finset.univ_unique,
      Finset.sum_singleton]
    constructor
    · rintro rfl i
      fin_cases i <;> simp
    · intro h
      have h0 := h 0
      have h1 := h 1
      simp at h0 h1
      funext u; cases u; linarith
  · intro x hx y hy i hi
    rw [Set.mem_singleton_iff] at hx hy
    subst hx hy
    simp at hi

theorem a_fails : ¬ (SBFR g ∧ TRFR g) := by
  rintro ⟨-, r, hr⟩
  have h1 := hr (fun _ => 0) 1
  have h2 := hr (fun _ => 0) 2
  simp only [g] at h1 h2
  norm_cast at h1 h2
  simp at h1 h2
  linarith

end SqCex

theorem solution : ¬ (∀ {V : Type} [Fintype V] [DecidableEq V] (g : (V → ℝ) → WithTop ℝ)
    (hdom : (DomR g).Nonempty),
    [SBFR g ∧ TRFR g,
     ∀ p ∈ DomR g, ZeroLR (fun d => DirDeriv g p d),
     ∀ p ∈ DomR g, MConvexPolyhedronR (SubDifferentialR g p),
     ∀ x : V → ℝ, (ArgMinR (LinearWeightR g (fun v => - x v))).Nonempty →
        LConvexPolyhedronR (ArgMinR (LinearWeightR g (fun v => - x v)))].TFAE) := by
  intro h
  have H := h SqCex.g ⟨fun _ => 0, by simp [DomR, SqCex.g]⟩
  exact SqCex.a_fails ((H.out 2 0).mp SqCex.c_holds)

#print axioms solution
