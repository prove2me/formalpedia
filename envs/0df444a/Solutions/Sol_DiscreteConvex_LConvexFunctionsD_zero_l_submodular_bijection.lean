-- Prove2me | solution 1 for DiscreteConvex.LConvexFunctionsD.zero_l_submodular_bijection
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:34:47.515725+00:00
-- url     : https://prove2.me/submissions/40b47b57-7834-4396-919c-efb9cba75f30

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_IsIntegerValued
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_ZeroLR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_ZeroLZZ
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_SubmodularSetFunction
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_LovaszExtension
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_InducedRho
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_InducedRhoZ

set_option autoImplicit false

open DiscreteConvex.LConvexFunctionsD

namespace ZeroLCex

/-- The constant `+∞` function on `ℝ^Unit`. -/
def gTop : (Unit → ℝ) → WithTop ℝ := fun _ => ⊤

theorem gTop_zeroL : ZeroLR gTop := by
  refine ⟨fun p q => le_top, ⟨0, fun p alpha => by simp [gTop]⟩, fun x t ht => ?_⟩
  simp [gTop, PosScalarMul, ht.ne']

theorem lovasz_zero : LovaszExtension (InducedRho gTop) (fun _ => 0) = 0 := by
  have hs : SortedValues (fun _ : Unit => (0 : ℝ)) = [0] := by
    unfold SortedValues
    rw [show Finset.image (fun _ : Unit => (0 : ℝ)) Finset.univ = {0} by
      ext; simp]
    exact Finset.sort_singleton _ _
  unfold LovaszExtension
  simp only [hs, List.length_singleton, Nat.sub_self, Finset.range_zero, Finset.sum_empty,
    zero_add]
  simp [PosScalarMul, InducedRho, gTop]

end ZeroLCex

theorem solution : ¬ (∀ {V : Type} [Fintype V] [DecidableEq V],
    (∀ g : (V → ℝ) → WithTop ℝ, ZeroLR g → LovaszExtension (InducedRho g) = g) ∧
    (∀ rho : Finset V → WithTop ℝ, SubmodularSetFunction rho → InducedRho (LovaszExtension rho) = rho) ∧
    (∀ g : (V → ℤ) → WithTop ℝ, ZeroLZZ g →
      (fun p : V → ℤ => LovaszExtension (InducedRhoZ g) (fun v => (p v : ℝ))) = g) ∧
    (∀ rho : Finset V → WithTop ℝ, SubmodularSetFunction rho → IsIntegerValued rho →
      InducedRhoZ (fun p : V → ℤ => LovaszExtension rho (fun v => (p v : ℝ))) = rho)) := by
  intro h
  have h1 := congrFun ((h (V := Unit)).1 ZeroLCex.gTop ZeroLCex.gTop_zeroL) (fun _ => 0)
  rw [ZeroLCex.lovasz_zero] at h1
  exact WithTop.zero_ne_top h1

#print axioms solution
