-- Prove2me | solution 1 for Formalism.L2.Th1.B.Sq.fExp_even
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:33:32.144803+00:00
-- url     : https://prove2.me/submissions/68478504-af68-4b5d-84aa-5ad7d0833991

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_WeierstrassReducedEquations
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffSig1S
import Theorems.Thm_Formalism_L2_Th1_B_Sq_even_iff_rescale
import Theorems.Thm_Formalism_L2_Th1_B_Sq_rescale_fExp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Sq
open PowerSeries
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.L2.Th1.B.Sq
theorem _root_.solution {f : PowerSeries K} (hf : constantCoeff f = 0)
    (h : ∀ n, Odd n → coeff n f = 0) : ∀ n, Odd n → coeff n (fExp f) = 0 := by
  rw [even_iff_rescale] at h ⊢
  rw [rescale_fExp _ hf, h]
end Formalism.L2.Th1.B.Sq
