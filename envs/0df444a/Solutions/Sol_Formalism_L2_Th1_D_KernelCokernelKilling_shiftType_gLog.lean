-- Prove2me | solution 1 for Formalism.L2.Th1.D.KernelCokernelKilling.shiftType_gLog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:00:14.914035+00:00
-- url     : https://prove2.me/submissions/a1822098-3d03-4250-a91d-a5e3e7b44f83

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_EqZeroOfPowEqOne
import Theorems.Thm_Formalism_L2_Th1_D_KernelCokernelKilling_constantCoeff_gLog
import Theorems.Thm_Formalism_L2_Th1_D_KernelCokernelKilling_gLog_shift
import Theorems.Thm_P2M_Formalism_L2_Th1_D_KernelCokernelKilling_integral_X__2606e57c7606
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_frobVar_eq_expand


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral letterLog entLog)
open Formalism.InvariantFactorPaths.G7 (frobVar frobVar_eq_expand UnrOK)
open Formalism.L2.Th1.D.KernelCokernelKilling
open MvPowerSeries
variable {K : Type} [NormedField K] {τ : Type}
namespace Formalism.L2.Th1.D.KernelCokernelKilling
theorem _root_.solution [DecidableEq τ] [CharZero K] {l d : ℕ} (hl : l.Prime) (σ : K →+* K) (φ : ZMod d → τ) :
    ShiftType l σ (fun s : ZMod d => gLog K l φ s) := by
  intro s
  refine ⟨constantCoeff_gLog hl.two_le φ s, ?_⟩
  have h := gLog_shift (K := K) hl (σ.comp σ) φ s
  show Integral (gLog K l φ s - C ((l : K)⁻¹) * frobVar (l ^ 2) (map (σ.comp σ) (gLog K l φ (s - 2))))
  rw [h]
  exact integral_X' _
end Formalism.L2.Th1.D.KernelCokernelKilling
