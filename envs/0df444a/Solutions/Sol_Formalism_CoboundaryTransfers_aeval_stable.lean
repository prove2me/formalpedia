-- Prove2me | solution 1 for Formalism.CoboundaryTransfers.aeval_stable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:30:47.253798+00:00
-- url     : https://prove2.me/submissions/91faafc3-b26e-4660-87dc-f18b03677bc1

import Definitions.Def_Formalism_CoboundaryTransfers_StatementAPI
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_TorsionKilledCriterionHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.CoboundaryTransfers
variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {B : Base O A} {M : ℕ}
  {D : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
namespace Formalism.CoboundaryTransfers
theorem _root_.solution (δ : D →ₗ[O] D) (S : Submodule O D) (hS : ∀ y ∈ S, δ y ∈ S)
    (f : Polynomial O) : ∀ y ∈ S, Polynomial.aeval δ f y ∈ S := by
  induction f using Polynomial.induction_on with
  | C a =>
    intro y hy
    rw [Polynomial.aeval_C, Module.algebraMap_end_apply]
    exact S.smul_mem a hy
  | add p q hp hq =>
    intro y hy
    rw [map_add, LinearMap.add_apply]
    exact S.add_mem (hp y hy) (hq y hy)
  | monomial n a ih =>
    intro y hy
    rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X, Module.End.mul_apply]
    exact ih _ (hS y hy)
end Formalism.CoboundaryTransfers
