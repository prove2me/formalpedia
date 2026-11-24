-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TBBx2.one_mem_UW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:57:32.915531+00:00
-- url     : https://prove2.me/submissions/eaac81d3-39b2-4574-9084-5050920dc27f

import Definitions.Def_Formalism_HermitianCurvature_StatementTBB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TriangleInequalityAtPlace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TBBx2
open MeasureTheory Filter Topology Formalism.QuantumDeterminants
open scoped ENNReal
noncomputable section
namespace Formalism.FourierDecayAlt.P.TBBx2
theorem _root_.solution (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) :
    (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ UWset k r z := by
  simp only [UWset, Set.mem_setOf_eq]
  refine ⟨?_, fun a => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩, Matrix.one_mulVec _⟩
  simp only [UH, Set.mem_setOf_eq, Matrix.conjTranspose_one, one_mul, mul_one]
end Formalism.FourierDecayAlt.P.TBBx2
