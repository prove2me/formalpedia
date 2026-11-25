-- Prove2me | solution 1 for Formalism.L2.SG.RowsOther.kppOff_of_termZero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:13:25.995275+00:00
-- url     : https://prove2.me/submissions/d97f0d76-0459-4e7a-878c-8f2e2a06dde9

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementPN
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RowsOther

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.RowsOther
open Formalism.FourierDecayAlt
variable {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : PB.Terms τ Rw I H H₁)
namespace Formalism.L2.SG.RowsOther
theorem _root_.solution (h : KppTermZero X) : KppOff X := by
  unfold KppOff PB.Terms.part
  have h0 : X.degSet.indicator X.op = 0 := by
    funext t
    exact Set.indicator_apply_eq_zero.2 (fun ht => h t ht)
  rw [h0]
  exact tsum_zero
end Formalism.L2.SG.RowsOther
