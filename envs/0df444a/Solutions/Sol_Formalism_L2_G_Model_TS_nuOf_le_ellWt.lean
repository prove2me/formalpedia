-- Prove2me | solution 1 for Formalism.L2.G.Model.TS.nuOf_le_ellWt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:10:13.666197+00:00
-- url     : https://prove2.me/submissions/f1607da0-a1b2-4478-8f35-338c91bf313e

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FormSK
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_FormSK
import Theorems.Thm_Formalism_L2_G_Model_TS_lastIdx_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Model Formalism.L2.G.Model.TS
open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.InvariantFactorPaths.INST
namespace Formalism.L2.G.Model.TS
theorem _root_.solution {m : ℕ} {lam : Fin (m + 1) → ℤ} (hl : Antitone lam) (t : Fin (m + 1)) :
    nuOf lam t ≤ ellWt lam := by
  unfold ellWt
  rw [lastIdx_succ]
  exact Int.toNat_le_toNat (sub_le_sub_right (hl (Fin.zero_le t)) _)
end Formalism.L2.G.Model.TS
