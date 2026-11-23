-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ScaleThresholdCharacters.scaleCharacter_ok
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:30:46.350644+00:00
-- url     : https://prove2.me/submissions/61119359-e74e-4812-9c5f-614d2c9d9daa

import Definitions.Def_Formalism_HermitianCurvature_LowerBlockNormalisedBoundFromComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScaleThresholdCharacters

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ScaleThresholdCharacters
open Formalism.FourierDecayAlt.PairingProductCorollary
namespace Formalism.FourierDecayAlt.P.ScaleThresholdCharacters
theorem _root_.solution : ScaleCharacter := by
  intro ka i l c hka hi
  have hk : (ka : ℂ) ≠ 0 := by exact_mod_cast hka.ne'
  have he : (3 - 2 * (i : ℤ)) + ((2 * i - 2 : ℕ) : ℤ) = 1 := by omega
  have h1 : (ka : ℂ) ^ (3 - 2 * (i : ℤ)) * (ka : ℂ) ^ (2 * i - 2) = ka := by
    rw [← zpow_natCast, ← zpow_add₀ hk, he, zpow_one]
  have h2 : (ka : ℂ) ^ (3 - 2 * (i : ℤ)) * l * ((ka : ℂ) ^ (2 * i - 2) * c) = (ka : ℂ) * (l * c) := by
    calc (ka : ℂ) ^ (3 - 2 * (i : ℤ)) * l * ((ka : ℂ) ^ (2 * i - 2) * c)
        = ((ka : ℂ) ^ (3 - 2 * (i : ℤ)) * (ka : ℂ) ^ (2 * i - 2)) * (l * c) := by ring
      _ = (ka : ℂ) * (l * c) := by rw [h1]
  rw [h2]
  congr 1
  simp only [map_mul, Complex.conj_ofReal]
  ring
end Formalism.FourierDecayAlt.P.ScaleThresholdCharacters
