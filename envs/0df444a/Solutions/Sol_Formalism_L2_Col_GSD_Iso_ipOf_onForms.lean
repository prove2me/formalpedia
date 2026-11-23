-- Prove2me | solution 1 for Formalism.L2.Col.GSD.Iso.ipOf_onForms
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:13:33.46185+00:00
-- url     : https://prove2.me/submissions/223261f0-26a1-42e0-a351-889c9ce5e974

import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DoubleCosetDecompositionAll
import Definitions.Def_Formalism_LocalToGlobal_Columns_GSetLemmas
import Theorems.Thm_Formalism_L2_Col_GSD_ipOf_eq_sum
import Theorems.Thm_Formalism_L2_Col_GSD_ipOf_indep
import Theorems.Thm_Formalism_L2_Col_GSD_Iso_card_stab

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
open Formalism.L2.Col.GSD Formalism.L2.Col.GSD.Iso
variable {S S' : GSD K} (e : GSD.Iso S S')
namespace Formalism.L2.Col.GSD.Iso
theorem _root_.solution (h : S.Ok) (h' : S'.Ok) (s : S.Sec) (s' : S'.Sec) (φ ψ : S.EqFun) :
    S'.ipOf h' s' (e.onForms φ) (e.onForms ψ) = S.ipOf h s φ ψ := by
  let _ := h.fintypeCl
  let _ := h'.fintypeCl
  rw [S'.ipOf_indep h' s' (e.mapSec s), GSD.ipOf_eq_sum, GSD.ipOf_eq_sum]
  refine Fintype.sum_equiv e.onCl.symm _ _ fun c' => ?_
  show ((Nat.card (MulAction.stabilizer S'.G (e.eD (s.rep (e.onCl.symm c')))) : K))⁻¹ *
    S'.pair (e.eV ((φ : S.D → S.V) (e.eD.symm (e.eD (s.rep (e.onCl.symm c'))))))
      (e.eV ((ψ : S.D → S.V) (e.eD.symm (e.eD (s.rep (e.onCl.symm c')))))) = _
  rw [e.card_stab, Equiv.symm_apply_apply, e.pair]
end Formalism.L2.Col.GSD.Iso
