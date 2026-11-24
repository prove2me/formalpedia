-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x5.vec_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:29:26.509319+00:00
-- url     : https://prove2.me/submissions/e03fb45a-eead-49fa-bdad-d246f0e4ceb2

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_idx_cases

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace Formalism.FourierDecayAlt.P.B2x5
theorem _root_.solution (k r' : ℕ) {u v : Fin (2 * (1 + r') + k + 1) → ℂ} (h0 : u (i0 k r') = v (i0 k r'))
    (h1 : res k r' u = res k r' v) (h2 : u (iL k r') = v (iL k r')) : u = v := by
  funext p
  rcases idx_cases k r' p with h | ⟨j, h⟩ | h
  · subst h; exact h0
  · subst h; exact congrFun h1 j
  · subst h; exact h2
end Formalism.FourierDecayAlt.P.B2x5
