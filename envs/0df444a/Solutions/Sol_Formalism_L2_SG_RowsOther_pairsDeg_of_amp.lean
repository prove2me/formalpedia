-- Prove2me | solution 1 for Formalism.L2.SG.RowsOther.pairsDeg_of_amp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:19:34.211951+00:00
-- url     : https://prove2.me/submissions/a6987e24-7b24-4564-ad0c-df228c7dc414

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementPN
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RowsOther
import Theorems.Thm_Formalism_L2_SG_RowsOther_pairAbs_le_ampSum

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
theorem _root_.solution (hG : 0 ≤ X.Gam1) (Pg du : ℝ) (k f : ℕ) (hPg : 0 ≤ Pg) (h : PairsDegAmp X Pg du k f) :
    PairsDeg X Pg du k f :=
  (mul_le_mul_of_nonneg_left (pairAbs_le_ampSum X hG _ h.1) hPg).trans h.2
end Formalism.L2.SG.RowsOther
