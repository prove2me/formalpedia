-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FlagGramRestriction.Phi_gram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:31:17.467084+00:00
-- url     : https://prove2.me/submissions/7932a8a1-2a2c-4b00-81d0-7f115fb96b38

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentUpperFacts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FlagGramRestriction

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
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.FlagGramRestriction
open C2x5 C2x6 C2x7 HermitianProjections FixedPointsGramVector UnipotentUpperFacts
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.FlagGramRestriction
theorem _root_.solution {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι] (H : Matrix n n ℂ)
    (V : Matrix n ι ℂ) (g : Matrix n n ℂ) (Φ : Matrix ι ι ℂ) (hg : gᴴ * H * g = H) (hgV : g * V = V * Φ) :
    Φᴴ * (Vᴴ * H * V) * Φ = Vᴴ * H * V := by
  calc Φᴴ * (Vᴴ * H * V) * Φ = (V * Φ)ᴴ * H * (V * Φ) := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = (g * V)ᴴ * H * (g * V) := by rw [hgV]
    _ = Vᴴ * (gᴴ * H * g) * V := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Vᴴ * H * V := by rw [hg]
end Formalism.FourierDecayAlt.P.FlagGramRestriction
