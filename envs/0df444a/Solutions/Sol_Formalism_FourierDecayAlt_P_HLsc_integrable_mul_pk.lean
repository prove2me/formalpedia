-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HLsc.integrable_mul_pk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:15:14.264364+00:00
-- url     : https://prove2.me/submissions/0ea08af5-a3e5-4b61-b610-9155294321b2

import Definitions.Def_Formalism_HermitianCurvature_StatementE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Herglotz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HerglotzLowerSemicontinuous
import Theorems.Thm_Formalism_FourierDecayAlt_P_HLsc_continuous_pk
import Theorems.Thm_Formalism_FourierDecayAlt_P_HLsc_pk_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_HLsc_pk_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HLsc
open Real Filter Topology Finset MeasureTheory Formalism.FourierDecayAlt.P.Herglotz
variable {d : ℕ}
namespace Formalism.FourierDecayAlt.P.HLsc
theorem _root_.solution {N : (Fin d → ℝ) → ℝ} (hint : Integrable N) (z₀ : Fin d → ℝ) (n : ℕ) :
    Integrable (fun z => N z * pk (z - z₀) ^ n) := by
  refine hint.mul_bdd (c := (4 ^ d) ^ n) ?_ (Eventually.of_forall (fun z => ?_))
  · exact ((continuous_pk.comp (continuous_id.sub continuous_const)).pow n).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (pow_nonneg (pk_nonneg _) n)]
    exact pow_le_pow_left₀ (pk_nonneg _) (pk_le _) n
end Formalism.FourierDecayAlt.P.HLsc
