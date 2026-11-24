-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.adj_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:04:54.270785+00:00
-- url     : https://prove2.me/submissions/27d98d27-32cd-416b-a07c-88fccc923698

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_unit_norm_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_adj_sub_norm
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_sel_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_sel_sub_le

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {t : ℝ × ℝ} (h1 : t.1 ∈ Set.Icc (1 / 2 : ℝ) 2) (h2 : t.2 ∈ Set.Icc (1 / 2 : ℝ) 2)
include h1 h2
namespace Formalism.FourierDecayAlt.P.B4
theorem _root_.solution (x : Bool × Mat k r) (hx : unitLie k r x.2) :
    ‖(adj t x).2 - x.2‖ ≤ 8 * 4 ^ r * (|t.1 - 1| + |t.2 - 1|) := by
  have a1 := adj_sub_norm (k := k) (sel_mem h1 h2 x.1) x.2
  have a2 := unit_norm_le hx
  have a3 := sel_sub_le t x.1
  calc ‖(adj t x).2 - x.2‖ ≤ 8 * 4 ^ r * |sel t x.1 - 1| * ‖x.2‖ := a1
    _ ≤ 8 * 4 ^ r * (|t.1 - 1| + |t.2 - 1|) * 1 := by gcongr
    _ = 8 * 4 ^ r * (|t.1 - 1| + |t.2 - 1|) := mul_one _
end Formalism.FourierDecayAlt.P.B4
