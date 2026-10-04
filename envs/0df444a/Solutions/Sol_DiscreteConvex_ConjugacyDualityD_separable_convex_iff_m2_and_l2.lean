-- Prove2me | solution 1 for DiscreteConvex.ConjugacyDualityD.separable_convex_iff_m2_and_l2
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:40:49.998289+00:00
-- url     : https://prove2.me/submissions/234f0b33-238d-4f67-a872-5a12c31eeebb

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_MNaturalConvex
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_LNaturalConvex
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_MNat2Convex
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_LNat2Convex
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_IsSeparableConvex

set_option autoImplicit false

open DiscreteConvex.ConjugacyDualityD

namespace SepCex

def fTop : (Unit → ℤ) → WithTop ℝ := fun _ => ⊤

theorem mnat : MNaturalConvex fTop := by
  intro x hx
  exfalso; apply hx
  simp [LiftedFunction, fTop]

theorem lnat : LNaturalConvex fTop :=
  ⟨fun _ _ => le_top, ⟨0, fun _ => by simp [LiftedFunctionL, fTop]⟩⟩

theorem not_sep : ¬ IsSeparableConvex fTop := by
  rintro ⟨psi, hpsi, hf⟩
  obtain ⟨x, hx⟩ := (hpsi ()).1
  have := hf (fun _ => x)
  simp only [Finset.univ_unique, Finset.sum_singleton, fTop] at this
  exact hx this.symm

end SepCex

theorem solution : ¬ (∀ {V : Type} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ),
    [MNat2Convex f ∧ LNat2Convex f, MNaturalConvex f ∧ LNaturalConvex f,
        IsSeparableConvex f].TFAE) := by
  intro h
  have H := (h SepCex.fTop).out 1 2
  exact SepCex.not_sep (H.mp (And.intro SepCex.mnat SepCex.lnat))

#print axioms solution
