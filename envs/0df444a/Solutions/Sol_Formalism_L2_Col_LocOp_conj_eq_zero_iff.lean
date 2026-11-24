-- Prove2me | solution 1 for Formalism.L2.Col.LocOp.conj_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:13:49.180804+00:00
-- url     : https://prove2.me/submissions/21ef1319-c404-4b06-b63d-798b6e759aa4

import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DoubleCosetDecompositionAll
import Definitions.Def_Formalism_LocalToGlobal_Columns_GSetLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Col
open Formalism.DivisionValues Formalism.L2.DIV
variable {K : Type} [Field K] [NumberField K] [StarRing K]
open Formalism.L2.Col.LocOp
variable {S S' : GSD K}
namespace Formalism.L2.Col.LocOp
theorem _root_.solution (g : S.G) (g' : S'.G) (k : S.V →ₗ[K] S'.V) :
    (S'.ρ g') ∘ₗ k ∘ₗ (S.ρ g) = 0 ↔ k = 0 := by
  have e1 : ∀ y, S.ρ g (S.ρ g⁻¹ y) = y := fun y => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have e2 : ∀ y, S'.ρ g'⁻¹ (S'.ρ g' y) = y := fun y => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  constructor
  · intro hk
    ext x
    have h1 := LinearMap.congr_fun hk (S.ρ g⁻¹ x)
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, e1] at h1
    have h2 := congrArg (S'.ρ g'⁻¹) h1
    rw [e2, map_zero] at h2
    rw [h2, LinearMap.zero_apply]
  · rintro rfl
    simp
end Formalism.L2.Col.LocOp
