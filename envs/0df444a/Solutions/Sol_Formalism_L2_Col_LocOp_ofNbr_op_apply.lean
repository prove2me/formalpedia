-- Prove2me | solution 1 for Formalism.L2.Col.LocOp.ofNbr_op_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:13:53.859578+00:00
-- url     : https://prove2.me/submissions/04ba006b-89ca-4890-884d-b7ed78dd8827

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
theorem _root_.solution (tr : S'.G →* S.G) (nb : S'.D → Finset S.D) (T : S.V →ₗ[K] S'.V)
    (hn : ∀ g d' d, tr g • d ∈ nb (g • d') ↔ d ∈ nb d') (hT : ∀ g x, T (S.ρ (tr g) x) = S'.ρ g (T x))
    (φ : S.EqFun) (d' : S'.D) :
    (((ofNbr tr nb T hn hT).op φ : S'.EqFun) : S'.D → S'.V) d' = ∑ d ∈ nb d', T ((φ : S.D → S.V) d) := by
  rw [op_apply]
  show (Finsupp.indicator (nb d') (fun _ _ => T)).sum (fun d k => k ((φ : S.D → S.V) d)) = _
  rw [Finsupp.sum_indicator_index _ (fun _ _ => by simp)]
end Formalism.L2.Col.LocOp
