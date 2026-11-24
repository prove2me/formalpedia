-- Prove2me | solution 1 for Formalism.L2.Th1.B.Fs.embed_pair_at_variable_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:22:08.156886+00:00
-- url     : https://prove2.me/submissions/ff4c8b0d-b2a5-430e-bec4-bce0e1b0d184

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_RealAdelicInertTransportTypeFormsEqAlt
import Theorems.Thm_Formalism_L2_Th1_B_Fs_embed_pair_X_one
import Theorems.Thm_Formalism_L2_Th1_B_Fs_emb_psubst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Fs
open Formalism.InvariantFactorPaths.G7 (at1)
variable {K : Type} [Field K] [CharZero K]
local notation "A3" => MvPowerSeries (Fin 3) K
namespace Formalism.L2.Th1.B.Fs
theorem _root_.solution (j k : Fin 3) (f : PowerSeries K) : emb j k (at1 1 f) = at1 k f := by
  rw [at1, emb_psubst j k f (by simp), embed_pair_X_one]; rfl
end Formalism.L2.Th1.B.Fs
