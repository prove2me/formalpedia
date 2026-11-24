-- Prove2me | solution 1 for Formalism.L2.Indef.IndefRows.Qpart_decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:20:19.095788+00:00
-- url     : https://prove2.me/submissions/4b1b83b4-5e26-4626-82df-f7f766a0bc96

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_JacquetSubsetSums_SeparationTR
import Definitions.Def_Formalism_DivisorInequality_StatementObj
import Definitions.Def_Formalism_QuotientMetricDivisors_DivIntoDualShift
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse
import Theorems.Thm_Formalism_L2_Indef_comap_indep
import Theorems.Thm_Formalism_L2_Indef_comap_iSup_top
import Theorems.Thm_Formalism_L2_Indef_IndefRows_Ep_decomp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Indef
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
variable {K : Type} [Field K] [NumberField K] [StarRing K]
open Formalism.L2.Indef.IndefRows
variable {Bs : DefBase K} {Df : DefSide Bs} (S : IndefRows Df)
include S
namespace Formalism.L2.Indef.IndefRows
theorem _root_.solution (wf : Df.WF) (t : Bs.Tup) : iSupIndep (S.Qpart t) ∧ (⨆ p, S.Qpart t p) = ⊤ := by
  obtain ⟨h1, h2⟩ := S.Ep_decomp wf
  exact ⟨comap_indep (S.ι t) (S.l1c.1 t) S.Ep h1, comap_iSup_top (S.ι t) (S.l1c.1 t) S.Ep h2⟩
end Formalism.L2.Indef.IndefRows
