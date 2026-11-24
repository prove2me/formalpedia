-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.matrix_coefficient_linear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:21:52.226471+00:00
-- url     : https://prove2.me/submissions/0f6a9433-fd74-4012-adb9-7b590aba1aad

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_ckOn_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_ckOn_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_ckOn_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_dLR_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_W_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_W_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_allLie_lr
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_length_lr
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_gN_rpow_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.B.CCLin := by
  intro k r E _ _ A m F F' c c' a hF hF'
  obtain ⟨hF, hb⟩ := hF
  obtain ⟨hF', hb'⟩ := hF'
  refine ⟨⟨ckOn_add hF hF', ?_⟩, ⟨ckOn_smul a hF, ?_⟩⟩
  · intro u v hu hv hlen g hg
    have hl : (lr u v).length ≤ m := by rw [length_lr]; exact hlen
    rw [dLR_eq, W_add _ (allLie_lr hu hv) (ckOn_mono hl hF) (ckOn_mono hl hF') g hg, ← dLR_eq, ← dLR_eq]
    calc gN g ^ A * ‖dLR u v F g + dLR u v F' g‖
        ≤ gN g ^ A * (‖dLR u v F g‖ + ‖dLR u v F' g‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) (gN_rpow_nonneg g A)
      _ = gN g ^ A * ‖dLR u v F g‖ + gN g ^ A * ‖dLR u v F' g‖ := by ring
      _ ≤ c + c' := add_le_add (hb u v hu hv hlen g hg) (hb' u v hu hv hlen g hg)
  · intro u v hu hv hlen g hg
    rw [dLR_eq, W_smul, ← dLR_eq, Pi.smul_apply, norm_smul]
    calc gN g ^ A * (‖a‖ * ‖dLR u v F g‖) = ‖a‖ * (gN g ^ A * ‖dLR u v F g‖) := by ring
      _ ≤ ‖a‖ * c := mul_le_mul_of_nonneg_left (hb u v hu hv hlen g hg) (norm_nonneg _)
end Formalism.FourierDecayAlt.P
