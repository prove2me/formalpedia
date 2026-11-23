-- Prove2me | solution 1 for FibreCount.card_fibre
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:33.306639+00:00
-- url     : https://prove2.me/submissions/04e0d12d-d94b-46ba-a9f5-bfeb6d5a81f2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitDensity_CardFibreCompl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
open FibreCount
namespace FibreCount
theorem _root_.solution {K V U : Type} [Field K] [Fintype K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [AddCommGroup U] [Module K U] (φ : V →ₗ[K] U) (a : U) (x0 : V)
    (hx0 : φ x0 = a) :
    Nat.card {x : V // φ x = a} = Fintype.card K ^ finrank K (LinearMap.ker φ) := by
  have e : {x : V // φ x = a} ≃ LinearMap.ker φ :=
    { toFun := fun x => ⟨x.1 - x0, by rw [LinearMap.mem_ker, map_sub, x.2, hx0, sub_self]⟩
      invFun := fun y => ⟨y.1 + x0, by rw [map_add, LinearMap.mem_ker.mp y.2, zero_add, hx0]⟩
      left_inv := fun x => Subtype.ext (sub_add_cancel _ _)
      right_inv := fun y => Subtype.ext (add_sub_cancel_right _ _) }
  haveI : Finite V := Module.finite_of_finite K
  rw [Nat.card_congr e, Module.natCard_eq_pow_finrank (K := K), Nat.card_eq_fintype_card]
end FibreCount
