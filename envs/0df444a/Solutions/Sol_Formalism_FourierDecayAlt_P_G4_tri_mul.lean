-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G4.tri_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:18.698814+00:00
-- url     : https://prove2.me/submissions/5766540a-2aa0-4d65-bf6f-54d5b89a14a0

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerBlockPoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism.FourierDecayAlt.G
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G4
namespace Formalism.FourierDecayAlt.P.G4
theorem _root_.solution {d : ℕ} {p q : Matrix (Fin d) (Fin d) ℂ} (hp : ∀ i j, j < i → p i j = 0)
    (hq : ∀ i j, j < i → q i j = 0) (i j : Fin d) (hij : j < i) : (p * q) i j = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases lt_or_ge k i with h | h
  · rw [hp _ _ h, zero_mul]
  · rw [hq _ _ (lt_of_lt_of_le hij h), mul_zero]
end Formalism.FourierDecayAlt.P.G4
