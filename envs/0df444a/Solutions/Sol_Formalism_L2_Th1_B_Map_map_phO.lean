-- Prove2me | solution 1 for Formalism.L2.Th1.B.Map.map_phO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:53:06.051801+00:00
-- url     : https://prove2.me/submissions/8c0f1b85-e413-46e9-9426-281555d69029

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_BaseChangeCompatible
import Theorems.Thm_P2M_Formalism_L2_Th1_B_Map_map_psubst__d587dd5fe1df
import Theorems.Thm_P2M_Formalism_L2_Th1_B_Map_map_fLog__61ca95a60c85
import Theorems.Thm_Formalism_L2_Th1_B_Map_map_lU
import Theorems.Thm_Formalism_L2_Th1_B_Map_map_sigS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Map
open Formalism.InvariantFactorPaths.G7 (at1 cob)
variable {K K' : Type} [Field K] [CharZero K] [Field K'] [CharZero K'] (j : K →+* K')
namespace Formalism.L2.Th1.B.Map
theorem _root_.solution (s2 : K) (P : PowerSeries K) {l : PowerSeries K}
    (h0 : PowerSeries.constantCoeff l = 0) (h1 : PowerSeries.coeff 1 l = 1) :
    PowerSeries.map j (phO s2 P l) = phO (j s2) (PowerSeries.map j P) (PowerSeries.map j l) := by
  have hd : PowerSeries.constantCoeff (Formalism.L2.Th1.B.lU l) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Formalism.L2.Th1.B.lU, PowerSeries.coeff_mk, zero_add, h1]
  unfold Formalism.L2.Th1.B.phO
  rw [map_sub, map_add, map_neg, map_psubst' j h0, map_sigS, map_mul,
    PowerSeries.map_C, map_div₀, map_ofNat, map_pow, map_fLog' j hd, map_lU]
end Formalism.L2.Th1.B.Map
