-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G4.superSum_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:08.723543+00:00
-- url     : https://prove2.me/submissions/cd23e9d8-a06a-41fc-a67a-3905086ddbf4

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
theorem _root_.solution {n : ℕ} {p q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hp : IsUpperUni p)
    (hq : IsUpperUni q) : superSum (p * q) = superSum p + superSum q := by
  simp only [superSum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_apply]
  have hne : i.castSucc ≠ i.succ := (Fin.castSucc_lt_succ).ne
  rw [Finset.sum_eq_add i.castSucc i.succ hne]
  · rw [hp.1, hq.1]; ring
  · intro k _ hk
    rcases lt_trichotomy k i.castSucc with h | h | h
    · rw [hp.2 _ _ h]; ring
    · exact absurd h hk.1
    · have : i.succ < k := by
        rcases lt_or_eq_of_le (Fin.castSucc_lt_iff_succ_le.1 h) with h' | h'
        · exact h'
        · exact absurd h'.symm hk.2
      rw [hq.2 _ _ this]; ring
  · simp
  · simp
end Formalism.FourierDecayAlt.P.G4
