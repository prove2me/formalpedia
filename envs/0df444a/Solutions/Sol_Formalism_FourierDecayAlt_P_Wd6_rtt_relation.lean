-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd6.rtt_relation
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:55:23.747352+00:00
-- url     : https://prove2.me/submissions/b24262fd-9c25-4537-a728-2d0f6eb66199

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_shifted_flip_position_relation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd6
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [Ring A] [Algebra K A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd6
theorem _root_.solution (a : S) (M N : M2 A) (D : K) (h : Rel M N D) :
    Rh0 a D * lift0 M * d0 (ins a (lift0 N)) = d0 (ins a (lift0 N)) * lift0 M * Rh0 a D := by
  unfold Rh0
  rw [smul_mul_assoc, smul_mul_assoc, mul_smul_comm, shifted_flip_position_relation a M N D h]
end Formalism.FourierDecayAlt.P.Wd6
