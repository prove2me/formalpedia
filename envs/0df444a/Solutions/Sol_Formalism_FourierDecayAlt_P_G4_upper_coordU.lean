-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G4.upper_coordU
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:43:36.685616+00:00
-- url     : https://prove2.me/submissions/5ee61aab-dbd4-43e4-8580-eb406f0b7e18

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
theorem _root_.solution {d : ℕ} {u : Matrix (Fin d) (Fin d) ℂ} (hu : IsUpperUni u) : upper (coordU u) = u := by
  ext i j
  rcases lt_trichotomy i j with h | h | h
  · simp [upper, strictUpper, coordU, h, h.ne]
  · subst h; simp [upper, strictUpper, hu.1]
  · simp [upper, strictUpper, h.ne', not_lt.2 h.le, hu.2 _ _ h]
end Formalism.FourierDecayAlt.P.G4
