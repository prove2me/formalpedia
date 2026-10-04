-- Prove2me | solution 1 for DiscreteConvex.LConvexFunctionsD.zero_l_induces_submodular
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T05:19:29.241789+00:00
-- url     : https://prove2.me/submissions/c05aed05-dc2b-48e8-a90a-5a8a349df34d

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_IsIntegerValued
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_ZeroLR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_ZeroLZZ
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_SubmodularSetFunction
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_InducedRho
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_InducedRhoZ

set_option autoImplicit false

open DiscreteConvex.LConvexFunctionsD in
/-- The constant `+∞` function is in `0L[R→R]` as formalized (no properness requirement). -/
theorem zeroLR_top_6ac2aed9 : ZeroLR (fun _ : (Unit → ℝ) => (⊤ : WithTop ℝ)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p q
    simp
  · exact ⟨0, fun p a => by simp⟩
  · intro x t ht
    show (⊤ : WithTop ℝ) = PosScalarMul t ⊤
    simp [PosScalarMul, ht.ne']

open DiscreteConvex.LConvexFunctionsD Classical in
open scoped Pointwise in
theorem solution : ¬ (∀ {V : Type} [Fintype V] [DecidableEq V],
    (∀ g : (V → ℝ) → WithTop ℝ, ZeroLR g → SubmodularSetFunction (InducedRho g)) ∧
    (∀ g : (V → ℤ) → WithTop ℝ, ZeroLZZ g →
      SubmodularSetFunction (InducedRhoZ g) ∧ IsIntegerValued (InducedRhoZ g))) := by
  intro h
  have h1 := ((h (V := Unit)).1 (fun _ => ⊤) zeroLR_top_6ac2aed9).1
  simp [InducedRho] at h1
