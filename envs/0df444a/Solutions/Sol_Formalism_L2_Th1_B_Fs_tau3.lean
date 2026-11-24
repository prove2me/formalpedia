-- Prove2me | solution 1 for Formalism.L2.Th1.B.Fs.tau3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:41:32.188628+00:00
-- url     : https://prove2.me/submissions/371ee08d-66c3-4339-a92f-923b30c11aaf

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_RealAdelicInertTransportTypeFormsEqAlt
import Theorems.Thm_Formalism_L2_Th1_B_Fs_embed_pair_X_zero
import Theorems.Thm_Formalism_L2_Th1_B_Fs_embed_pair_X_one
import Theorems.Thm_Formalism_L2_Th1_B_Fs_embed_pair_at_variable_zero
import Theorems.Thm_Formalism_L2_Th1_B_Fs_embed_pair_at_variable_one
import Theorems.Thm_Formalism_L2_Th1_B_Fs_emb_atD
import Theorems.Thm_Formalism_L2_Th1_B_Fs_emb_wpDiff
import Theorems.Thm_Formalism_L2_Th1_B_Fs_pd_emb_0
import Theorems.Thm_Formalism_L2_Th1_B_Fs_pd_emb_1

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
theorem _root_.solution (hT : TauRule) {g2 g3 : K} {P : PowerSeries K} (hP : IsWp g2 g3 P) {j k : Fin 3}
    (hjk : j ≠ k) :
    (MvPowerSeries.X j - MvPowerSeries.X k) * (pd j (wp3 P j k) - pd k (wp3 P j k)) =
      wp3 P j k * (2 + 2 * (MvPowerSeries.X j - MvPowerSeries.X k) *
        (evalDiffThree j k (dz (sigS P)) - at1 j (dz (sigS P)) + at1 k (dz (sigS P)))) := by
  have h := congrArg (emb j k) (hT K g2 g3 P hP)
  simp only [map_add, map_sub, map_mul, map_ofNat, embed_pair_X_zero, embed_pair_X_one, embed_pair_at_variable_zero, embed_pair_at_variable_one, emb_atD,
    emb_wpDiff, ← pd_emb_0 hjk, ← pd_emb_1 hjk] at h
  exact h
end Formalism.L2.Th1.B.Fs
