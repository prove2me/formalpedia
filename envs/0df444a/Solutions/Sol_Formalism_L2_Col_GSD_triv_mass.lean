-- Prove2me | solution 1 for Formalism.L2.Col.GSD.triv_mass
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:07:21.056845+00:00
-- url     : https://prove2.me/submissions/fe65cc11-78d3-4c9f-b667-e870e4301fb1

import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DoubleCosetDecompositionAll
import Definitions.Def_Formalism_LocalToGlobal_Columns_GSetLemmas
import Theorems.Thm_Formalism_L2_Col_GSD_ipOf_eq_sum
import Theorems.Thm_Formalism_L2_Col_GSD_card_rep
import Theorems.Thm_Formalism_L2_Col_GSD_card_none
import Theorems.Thm_Formalism_L2_Col_GSD_card_some
import Theorems.Thm_Formalism_L2_DIV_CSD_pairOne_apply


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
variable (K)
namespace Formalism.L2.Col.GSD
theorem _root_.solution : (tv K).ip (tv_ok K) (fun _ => (1 : K)) (fun _ => (1 : K)) = 3 / 2 := by
  unfold GSD.ip
  rw [GSD.ipOf_eq_sum]
  let _ := (tv_ok K).fintypeCl
  rw [← (eCl K).symm.sum_comp, Fintype.sum_bool]
  have e1 : (eCl K).symm true = (tv K).cls (some 1) := (eCl K).symm_apply_eq.mpr rfl
  have e0 : (eCl K).symm false = (tv K).cls none := (eCl K).symm_apply_eq.mpr rfl
  rw [e1, e0, card_rep, card_rep, card_none, card_some, CSD.pairOne_apply]
  norm_num
end Formalism.L2.Col.GSD
