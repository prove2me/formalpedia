-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.al_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:44:54.883023+00:00
-- url     : https://prove2.me/submissions/ae6c7de5-4240-4105-a4ea-78bd32776afb

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x8
theorem _root_.solution {k r : ℕ} {g h : Mat k r} (hg : g ∈ GV k r) (hh : h ∈ GV k r) : g * h ∈ GV k r := by
  show (g * h)ᴴ * Hpk k r * (g * h) = Hpk k r
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hh' : hᴴ * Hpk k r * h = Hpk k r := hh
  rw [Matrix.conjTranspose_mul]
  calc hᴴ * gᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h := by simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [hg', hh']
end Formalism.FourierDecayAlt.P.B2x8
