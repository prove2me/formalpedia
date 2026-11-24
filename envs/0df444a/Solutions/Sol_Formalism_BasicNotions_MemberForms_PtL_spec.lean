-- Prove2me | solution 1 for Formalism.BasicNotions.MemberForms.PtL_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:55:46.575331+00:00
-- url     : https://prove2.me/submissions/807ceabf-cd39-4c27-8ecb-2cb033498322

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_Params
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_LocalRingCardinality_DataCoeff
import Definitions.Def_Formalism_LocalRingCardinality_DataArith
import Definitions.Def_Formalism_LocalRingCardinality_DataKernels
import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Formalism_LocalRingCardinality_DataForms
import Theorems.Thm_Formalism_BasicNotions_descend_spec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions
open NumberField
open Formalism.BasicNotions.MemberForms
attribute [instance] MemberForms.lvAcg MemberForms.lvMod MemberForms.lkAcg MemberForms.lkMod
  MemberForms.clsPFin MemberForms.stabPGrp MemberForms.stabPFin
variable {R : Ranks} {LL : Type} [Field LL] [NumberField LL] [StarRing LL] {embLL : LL →+* ℂ}
  {Pl : Rows.Places LL} {Tau : Type} [Fintype Tau] {hc : Tau → HCParam R}
  {C : ColumnChain R Tau hc} {A : ColumnsAtT R C} {P : PeriodMap R C}
  (M : MemberForms LL embLL Pl Tau hc C A P)
namespace Formalism.BasicNotions.MemberForms
theorem _root_.solution (h : M.PRat) (x : (M.lat R.m).V) :
    M.ptEmb (M.PtL h x) = P.lowerMap (P.evz (M.emb R.m x)) :=
  descend_spec (M.emb R.m) M.ptEmb M.ptEmb_inj (P.lowerMap ∘ₗ P.evz) h x
end Formalism.BasicNotions.MemberForms
