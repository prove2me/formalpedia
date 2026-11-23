-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StandardCharacterExists.poly_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:31:04.027199+00:00
-- url     : https://prove2.me/submissions/a35a2240-642c-43e1-be32-9cd5742525b1

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StandardCharacterExists

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G Matrix MeasureTheory Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StandardCharacterExists
namespace Formalism.FourierDecayAlt.P.StandardCharacterExists
theorem _root_.solution (m : ℕ) (c : ℕ → ℂ) : ∑ j ∈ Finset.range (m + 1), c j * (0 : ℂ) ^ (m - j) = c m := by
  rw [Finset.sum_eq_single m]
  · simp
  · intro j hj hne
    have : j < m + 1 := Finset.mem_range.mp hj
    rw [zero_pow (by omega), mul_zero]
  · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self m)) h
end Formalism.FourierDecayAlt.P.StandardCharacterExists
