-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxDs5.castW_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:50:08.091018+00:00
-- url     : https://prove2.me/submissions/342df489-190c-453e-9321-26545facdeeb

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselDomainMeasurable
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BFCell
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LastLevelSliceOfScalar
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxDs5_castW_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxDs5_castW_ct
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxDs5_hb_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxDs5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k : ℕ}
namespace Formalism.FourierDecayAlt.P.JFxDs5
theorem _root_.solution {μ : B.Mat k 0} (hμ : μ ∈ GV k 0) : (castW μ)ᴴ * Hb k * castW μ = Hb k := by
  have h : μᴴ * Hpk k 0 * μ = Hpk k 0 := hμ
  rw [hb_eq, castW_ct, ← castW_mul, ← castW_mul, h]
end Formalism.FourierDecayAlt.P.JFxDs5
