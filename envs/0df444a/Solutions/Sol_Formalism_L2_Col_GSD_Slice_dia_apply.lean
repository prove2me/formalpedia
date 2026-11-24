-- Prove2me | solution 1 for Formalism.L2.Col.GSD.Slice.dia_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:13:49.136262+00:00
-- url     : https://prove2.me/submissions/efd4476f-d5c1-466e-bb2d-1ae9cdd05167

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
open Formalism.L2.Col.GSD
variable (S : GSD K)
variable (A : Type) [Group A] [MulAction A S.D]
open Formalism.L2.Col.GSD.Slice
variable {S A} (σ : S.Slice A)
variable [SMulCommClass A S.G S.D]
namespace Formalism.L2.Col.GSD.Slice
theorem _root_.solution (b : A) (φ : S.EqFun) (d : S.D) :
    (((dia S b).op φ : S.EqFun) : S.D → S.V) d = (φ : S.D → S.V) (b • d) := by
  show (Finsupp.single (b • d) (LinearMap.id : S.V →ₗ[K] S.V)).sum (fun d k => k ((φ : S.D → S.V) d)) = _
  rw [Finsupp.sum_single_index]
  · rfl
  · simp
end Formalism.L2.Col.GSD.Slice
