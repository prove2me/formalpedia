-- Prove2me | solution 1 for Formalism.L2.SG.RowsOther.diag_of_abstract
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:00:09.827585+00:00
-- url     : https://prove2.me/submissions/d85f417b-3761-4f89-9213-f5c125effc35

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementPN
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RowsOther
import Theorems.Thm_Formalism_L2_SG_RowsOther_noId_idZero
import Theorems.Thm_Formalism_L2_SG_RowsOther_nonIdentity_K0

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
theorem _root_.solution [CompleteSpace H₁] (hA : PB.PairBoundAbstract) (hP : PB.NormSqBoundOfEqualIota)
    (hE : PB.GramSumLeOfPosSemidef) (hS : PB.PairSplit) (hSub : PB.SubFamily) (one : H) (Pg A ε ε' dd : ℝ)
    (hPg : 0 ≤ Pg) (hdd : 0 ≤ dd) (hAbs : X.AbsConv)
    (hN : X.NormExpansionOn X.genSet ∧ X.NormExpansionOn X.ngSet) (hG : X.GGBound Pg)
    (hO : X.RowOrth) (hC : X.CorankPos) (hI : IdOne X one) (h1 : X.RowBig ε dd)
    (h2 : X.RowNotScalar ε dd) (h3 : X.RowMain A dd) (h4 : X.RowNG ε' dd) :
    DiagRow X one ((√(Pg * (A + 2 * ε)) + √(Pg * (ε + ε'))) ^ 2) dd := by
  unfold DiagRow
  rw [← nonIdentity_K0 X one hI]
  exact hA hP hE hS hSub τ Rw I H H₁ (noId X) Pg A ε ε' dd hPg hdd hAbs hN hG hO hC (noId_idZero X) h1 h2 h3 h4
end Formalism.L2.SG.RowsOther
