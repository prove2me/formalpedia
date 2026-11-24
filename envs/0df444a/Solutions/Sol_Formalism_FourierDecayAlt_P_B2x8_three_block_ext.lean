-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.three_block_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:04:54.744957+00:00
-- url     : https://prove2.me/submissions/b6fd803e-2568-47ba-97b0-0d987bf22d9f

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_three_block_eta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x8
theorem _root_.solution {u v : Fin (2 * (1 + r') + k + 1) → ℂ} (h1 : u (tkF k r') = v (tkF k r'))
    (h2 : ∀ j, u (levPos k 1 r' j) = v (levPos k 1 r' j)) (h3 : u (tkL k r') = v (tkL k r')) : u = v := by
  calc u = mk3 k r' (cF u) (mid u) (cL u) := (three_block_eta u).symm
    _ = mk3 k r' (cF v) (mid v) (cL v) := by
      rw [show cF u = cF v from h1, show mid u = mid v from funext h2, show cL u = cL v from h3]
    _ = v := three_block_eta v
end Formalism.FourierDecayAlt.P.B2x8
