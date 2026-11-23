-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G4.tri_mul_diag
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:43:20.925545+00:00
-- url     : https://prove2.me/submissions/952a61f4-067f-46c4-8e34-0a5019ccf2db

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
    (hq : ∀ i j, j < i → q i j = 0) (i : Fin d) : (p * q) i i = p i i * q i i := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun k _ hk => ?_) (by simp)
  rcases lt_or_gt_of_ne hk with h | h
  · rw [hp _ _ h, zero_mul]
  · rw [hq _ _ h, mul_zero]
end Formalism.FourierDecayAlt.P.G4
