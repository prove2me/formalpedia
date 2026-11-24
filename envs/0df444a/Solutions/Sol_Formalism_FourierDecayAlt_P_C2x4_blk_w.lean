-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.C2x4.blk_w
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:36:35.372801+00:00
-- url     : https://prove2.me/submissions/dd6e9c91-67c0-4851-b774-3b15c4a53d09

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerAntidiagonalExact
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerFourthCondition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RelevantMonotoneOfParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x4_cut_preserves

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.C2x4
variable {m : ℕ}
namespace Formalism.FourierDecayAlt.P.C2x4
theorem _root_.solution (w : Equiv.Perm (Fin m)) (a : Fin m) : blk w (w a) = blk w a := by
  unfold blk
  congr 1
  ext c
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    by_contra h; push_neg at h
    have := (cut_preserves w c h2 a).mp h
    exact absurd h1 (not_lt.mpr this)
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    by_contra h; push_neg at h
    have := (cut_preserves w c h2 a).mpr h
    exact absurd h1 (not_lt.mpr this)
end Formalism.FourierDecayAlt.P.C2x4
