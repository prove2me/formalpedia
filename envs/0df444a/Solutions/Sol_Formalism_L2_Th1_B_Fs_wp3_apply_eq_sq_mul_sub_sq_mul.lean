-- Prove2me | solution 1 for Formalism.L2.Th1.B.Fs.wp3_apply_eq_sq_mul_sub_sq_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:41:41.476175+00:00
-- url     : https://prove2.me/submissions/c4b67ed8-326b-47d1-9fd0-96115001b7fb

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_RealAdelicInertTransportTypeFormsEqAlt
import Theorems.Thm_Formalism_L2_Th1_B_Fs_embed_pair_X_zero
import Theorems.Thm_Formalism_L2_Th1_B_Fs_embed_pair_X_one
import Theorems.Thm_Formalism_L2_Th1_B_Fs_emb_wpDiff
import Theorems.Thm_Formalism_L2_Th1_B_Fs_emb_fExp
import Theorems.Thm_Formalism_L2_Th1_B_Add0_wpDiff_eq
import Theorems.Thm_Formalism_L2_Th1_B_addSigmaLog
import Theorems.Thm_Formalism_L2_Th1_B_constantCoeff_fLog
import Theorems.Thm_Formalism_L2_Th1_B_dqRule
import Theorems.Thm_Formalism_L2_Th1_B_fExp_fLog


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
theorem _root_.solution {g2 g3 : K} {P : PowerSeries K} (hP : IsWp g2 g3 P) (j k : Fin 3) :
    wp3 P j k = (MvPowerSeries.X j ^ 2 - MvPowerSeries.X k ^ 2) *
      fExp (emb j k (par0 (sigS P))) := by
  have hN1 : MvPowerSeries.constantCoeff
      (1 - MvPowerSeries.X 0 ^ 2 * MvPowerSeries.X 1 ^ 2 * dq P : MvPowerSeries (Fin 2) K) = 1 := by
    simp
  have c0 : MvPowerSeries.constantCoeff (par0 (sigS P)) = 0 := by
    rw [addSigmaLog K g2 g3 P hP]; exact constantCoeff_fLog hN1
  rw [← emb_wpDiff, Add0.wpDiff_eq dqRule hP.2.1, ← fExp_fLog hN1, ← addSigmaLog K g2 g3 P hP,
    map_mul, emb_fExp j k c0, map_sub, map_pow, map_pow, embed_pair_X_zero, embed_pair_X_one]
end Formalism.L2.Th1.B.Fs
