-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.adj_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:04:58.913819+00:00
-- url     : https://prove2.me/submissions/16285485-55c0-44cb-a04f-310b99d60f39

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_unit_norm_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_adj_norm
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_sel_mem

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
theorem _root_.solution (x : Bool × Mat k r) (hx : unitLie k r x.2) : ‖(adj t x).2‖ ≤ 4 ^ r := by
  have a1 := adj_norm (k := k) (sel_mem h1 h2 x.1) x.2
  have a2 := unit_norm_le hx
  calc ‖(adj t x).2‖ ≤ 4 ^ r * ‖x.2‖ := a1
    _ ≤ 4 ^ r * 1 := by gcongr
    _ = 4 ^ r := mul_one _
end Formalism.FourierDecayAlt.P.B4
