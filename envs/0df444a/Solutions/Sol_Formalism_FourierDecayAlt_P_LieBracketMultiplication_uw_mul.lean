-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LieBracketMultiplication.uw_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:32:14.981522+00:00
-- url     : https://prove2.me/submissions/3fb37ee1-3bf0-4e4b-a719-ccf99d1ca201

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeftDerivativeCurves
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieBracketMultiplication

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.QrD
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.LieBracketMultiplication
variable {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}
namespace Formalism.FourierDecayAlt.P.LieBracketMultiplication
theorem _root_.solution {g h : Mx k r} (hg : g ∈ UWset k r z) (hh : h ∈ UWset k r z) : g * h ∈ UWset k r z := by
  obtain ⟨hg1, hg2, hg3⟩ := hg
  obtain ⟨hh1, hh2, hh3⟩ := hh
  refine ⟨?_, fun a => ⟨?_, ?_⟩, ?_⟩
  · have e1 : gᴴ * Hpk k r * g = Hpk k r := hg1
    have e2 : hᴴ * Hpk k r * h = Hpk k r := hh1
    show (g * h)ᴴ * Hpk k r * (g * h) = Hpk k r
    rw [Matrix.conjTranspose_mul]
    calc hᴴ * gᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h := by simp only [Matrix.mul_assoc]
      _ = Hpk k r := by rw [e1, e2]
  · rw [← Matrix.mulVec_mulVec, (hh2 a).1, (hg2 a).1]
  · rw [← Matrix.mulVec_mulVec, (hh2 a).2, (hg2 a).2]
  · rw [← Matrix.mulVec_mulVec, hh3, hg3]
end Formalism.FourierDecayAlt.P.LieBracketMultiplication
