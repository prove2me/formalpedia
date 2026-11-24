-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.C2x7.N_sub_S
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:30:56.179345+00:00
-- url     : https://prove2.me/submissions/8efe2768-e72c-4942-b86f-984d29ef0f09

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MajorantEstimate
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LinearChangeOfVariablesBis
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x7_one_mem_UW

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants MeasureTheory
open scoped ComplexConjugate ENNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.C2x7
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.C2x7
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ} {n : B.Mat k r} (hn : n ∈ Nset k r) : n ∈ Sset k r z :=
  ⟨1, one_mem_UW z, n, hn, by simp⟩
end Formalism.FourierDecayAlt.P.C2x7
