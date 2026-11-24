-- Prove2me | solution 1 for Formalism.L2.Th1.B.Fs.emb_wpDiff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:32:59.008491+00:00
-- url     : https://prove2.me/submissions/f1404347-966f-494d-b659-aa90cd32be30

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_RealAdelicInertTransportTypeFormsEqAlt
import Theorems.Thm_Formalism_L2_Th1_B_Fs_embed_pair_X_zero
import Theorems.Thm_Formalism_L2_Th1_B_Fs_embed_pair_X_one
import Theorems.Thm_Formalism_L2_Th1_B_Fs_embed_pair_at_variable_zero
import Theorems.Thm_Formalism_L2_Th1_B_Fs_embed_pair_at_variable_one

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
theorem _root_.solution (j k : Fin 3) (P : PowerSeries K) : emb j k (wpDiff P) = wp3 P j k := by
  simp only [wpDiff, wp3, map_add, map_sub, map_mul, map_pow, embed_pair_X_zero, embed_pair_X_one, embed_pair_at_variable_zero,
    embed_pair_at_variable_one]
end Formalism.L2.Th1.B.Fs
