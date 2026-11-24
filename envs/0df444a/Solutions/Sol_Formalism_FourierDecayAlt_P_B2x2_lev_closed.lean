-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x2.lev_closed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:01:27.675794+00:00
-- url     : https://prove2.me/submissions/f633d42d-86ad-4a56-8a39-a26040e06e9e

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_blk_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_blk_lev
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_lev_cont

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x2
namespace Formalism.FourierDecayAlt.P.B2x2
theorem _root_.solution (k r' : ℕ) (U : Set (Mat k r')) (hU : IsClosed U) : IsClosed (ιLev k 1 r' '' U) := by
  have e : ιLev k 1 r' '' U = {y | ιLev k 1 r' (blk k r' y) = y} ∩ blk k r' ⁻¹' U := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨?_, ?_⟩
      · show ιLev k 1 r' (blk k r' (ιLev k 1 r' x)) = ιLev k 1 r' x
        rw [blk_lev]
      · show blk k r' (ιLev k 1 r' x) ∈ U
        rw [blk_lev]
        exact hx
    · rintro ⟨h1, h2⟩
      exact ⟨blk k r' y, h2, h1⟩
  rw [e]
  exact (isClosed_eq ((lev_cont k r').comp (blk_cont k r')) continuous_id).inter
    (hU.preimage (blk_cont k r'))
end Formalism.FourierDecayAlt.P.B2x2
