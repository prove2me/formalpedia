-- Prove2me | solution 1 for Claim.gamma_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:28:52.401586+00:00
-- url     : https://prove2.me/submissions/f66115ba-b935-445c-9e3e-6fc8dd57a960

import Definitions.Def_Development_AutomorphicArithmetic_CharacterBoxes_HalfPlane
import Definitions.Def_Development_AutomorphicArithmetic_CharacterBoxes_ClaimStrip

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open Claim
namespace Claim
theorem _root_.solution {M : ℕ} [NeZero M] (φ : DirichletCharacter ℂ M) {t : ℂ} (ht : 0 < t.re) :
    DirichletCharacter.gammaFactor φ t ≠ 0 := by
  rcases φ.even_or_odd with hφ | hφ
  · rw [hφ.gammaFactor_def]; exact Complex.Gammaℝ_ne_zero_of_re_pos ht
  · rw [hφ.gammaFactor_def]
    exact Complex.Gammaℝ_ne_zero_of_re_pos (by rw [Complex.add_re, Complex.one_re]; linarith)
end Claim
