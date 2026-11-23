-- Prove2me | solution 1 for Formalism.LIFT.CocyclePolynomialSubmodules.aeval_pres
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:35:28.079465+00:00
-- url     : https://prove2.me/submissions/8f1d5bc5-54dd-4b29-9358-9741c01818af

import Definitions.Def_Formalism_LagrangeIdealLifts_Statement
import Definitions.Def_Formalism_WindowSums_AnnihilatorPolynomials_ZpowVal
import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_UClaim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LIFT
open Formalism.LIFT.CocyclePolynomialSubmodules
namespace Formalism.LIFT.CocyclePolynomialSubmodules
theorem _root_.solution {R E : Type} [CommRing R] [AddCommGroup E] [Module R E] (f : E →ₗ[R] E)
    (S : Submodule R E) (hf : ∀ y ∈ S, f y ∈ S) (p : Polynomial R) :
    ∀ y ∈ S, Polynomial.aeval f p y ∈ S := by
  intro y hy
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, LinearMap.add_apply]
    exact S.add_mem hp hq
  | monomial n a =>
    rw [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    apply S.smul_mem
    induction n with
    | zero =>
      rw [pow_zero, Module.End.one_apply]
      exact hy
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact hf _ ih
end Formalism.LIFT.CocyclePolynomialSubmodules
