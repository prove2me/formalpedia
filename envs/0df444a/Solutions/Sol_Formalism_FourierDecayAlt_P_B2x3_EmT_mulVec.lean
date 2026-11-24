-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x3.EmT_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:57:22.622809+00:00
-- url     : https://prove2.me/submissions/4a6caa2b-6f93-4b4a-a891-82a1b5dc47da

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x3
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x3
theorem _root_.solution (z : Fin (2 * r + k + 1) → ℂ) (m : Fin (k + 1)) : ((Em k r)ᵀ *ᵥ z) m = z (wI k r m) := by
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (wI k r m)]
  · rw [Matrix.transpose_apply, Em, if_pos rfl, one_mul]
  · intro b _ hb
    rw [Matrix.transpose_apply, Em, if_neg hb, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h
end Formalism.FourierDecayAlt.P.B2x3
