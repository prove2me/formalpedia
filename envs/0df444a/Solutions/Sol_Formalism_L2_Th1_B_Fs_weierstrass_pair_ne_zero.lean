-- Prove2me | solution 1 for Formalism.L2.Th1.B.Fs.weierstrass_pair_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:51:37.74881+00:00
-- url     : https://prove2.me/submissions/20c6cadf-a5a4-4ef1-b003-57eb2ffa1c33

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_RealAdelicInertTransportTypeFormsEqAlt
import Theorems.Thm_Formalism_L2_Th1_B_Fs_sigS_cc
import Theorems.Thm_Formalism_L2_Th1_B_Fs_wp3_apply_eq_sq_mul_sub_sq_mul
import Theorems.Thm_Formalism_L2_Th1_B_Fs_sq_sub_ne_zero
import Theorems.Thm_Formalism_L2_Th1_B_Fs_fExp_ne_zero
import Theorems.Thm_Formalism_L2_Th1_B_Fs_constantCoeff_parallelogram_defect
import Theorems.Thm_Formalism_L2_Th1_B_Fs_emb_cc
import Theorems.Thm_Formalism_L2_Th1_B_Add0_sigS_cc


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
theorem _root_.solution {g2 g3 : K} {P : PowerSeries K} (hP : IsWp g2 g3 P) {j k : Fin 3}
    (hjk : j ≠ k) : wp3 P j k ≠ 0 := by
  rw [wp3_apply_eq_sq_mul_sub_sq_mul hP]
  exact mul_ne_zero (sq_sub_ne_zero hjk) (fExp_ne_zero (emb_cc j k (constantCoeff_parallelogram_defect (sigS_cc P))))
end Formalism.L2.Th1.B.Fs
