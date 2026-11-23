-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz2.geom_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:43:40.776446+00:00
-- url     : https://prove2.me/submissions/b7384559-0e50-48bf-99b0-b740a23e4212

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz2_geom_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz2
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz2
theorem _root_.solution (k n : ℕ) : ∑ j ∈ Ioc k n, 1 / (2 : ℝ) ^ j ≤ 1 / 2 ^ k := by
  rcases le_total k n with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [geom_eq]
    have : (0 : ℝ) < 1 / 2 ^ (k + d) := by positivity
    linarith
  · rw [Finset.Ioc_eq_empty (by omega)]
    simp
end Formalism.FourierDecayAlt.P.Sz2
