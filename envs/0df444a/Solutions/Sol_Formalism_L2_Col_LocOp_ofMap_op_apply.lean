-- Prove2me | solution 1 for Formalism.L2.Col.LocOp.ofMap_op_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:14:12.947453+00:00
-- url     : https://prove2.me/submissions/4d1dfcff-6323-4e1a-802e-e9fffdcce28d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumBridge
import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
import Theorems.Thm_Formalism_L2_Col_LocOp_op_apply

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
attribute [instance] GSD.grpG GSD.actD GSD.addV GSD.modV GSD.modOV GSD.towV GSD.finιV GSD.decιV
variable {K : Type} [Field K] [NumberField K] [StarRing K]
open Formalism.L2.Col.LocOp
variable {S S' : GSD K} (A : LocOp S S')
namespace Formalism.L2.Col.LocOp
theorem _root_.solution (tr : S'.G →* S.G) (p : S'.D → S.D) (T : S.V →ₗ[K] S'.V)
    (hp : ∀ g d', p (g • d') = tr g • p d') (hT : ∀ g x, T (S.ρ (tr g) x) = S'.ρ g (T x)) (φ : S.EqFun)
    (d' : S'.D) : (((ofMap tr p T hp hT).op φ : S'.EqFun) : S'.D → S'.V) d' = T ((φ : S.D → S.V) (p d')) := by
  rw [op_apply]
  show (Finsupp.single (p d') T).sum (fun d k => k ((φ : S.D → S.V) d)) = _
  rw [Finsupp.sum_single_index]
  simp
end Formalism.L2.Col.LocOp
