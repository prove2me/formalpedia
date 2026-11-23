-- Prove2me | solution 1 for Formalism.L2.Col.ClsKer.term_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:08:51.881802+00:00
-- url     : https://prove2.me/submissions/888822f5-24dc-4918-9f35-f4df9bd53667

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
open Formalism.L2.Col.ClsKer
variable {S S' : GSD K} (A : ClsKer S S')
namespace Formalism.L2.Col.ClsKer
theorem _root_.solution (φ : S.EqFun) (g : S.G) (d : S.D) (d' : S'.D) :
    A.k (g • d) d' ((φ : S.D → S.V) (g • d)) = A.k d d' ((φ : S.D → S.V) d) := by
  have e1 : ∀ y, S.ρ g⁻¹ (S.ρ g y) = y := fun y => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have h1 := A.equiv g 1 d d'
  rw [one_smul, map_one] at h1
  rw [h1, φ.2]
  simp only [LinearMap.comp_apply, Module.End.one_apply, e1]
end Formalism.L2.Col.ClsKer
