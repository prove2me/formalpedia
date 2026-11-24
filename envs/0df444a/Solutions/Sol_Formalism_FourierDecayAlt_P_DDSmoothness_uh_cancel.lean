-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DDSmoothness.uh_cancel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:12:45.856627+00:00
-- url     : https://prove2.me/submissions/4279784a-2627-4779-8126-e648d6dddfeb

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothAdd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UhMeasurableSet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate
noncomputable section
set_option maxHeartbeats 1600000
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DDSmoothness
open Formalism.FourierDecayAlt.ThreeDimData
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.DDSmoothness
theorem _root_.solution {a x : Mx k r} (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hax : a * x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
  have ha' : aᴴ * Formalism.QuantumDeterminants.Hpk k r * a = Formalism.QuantumDeterminants.Hpk k r := ha
  have hax' : (a * x)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * x) = Formalism.QuantumDeterminants.Hpk k r := hax
  show xᴴ * Formalism.QuantumDeterminants.Hpk k r * x = Formalism.QuantumDeterminants.Hpk k r
  calc xᴴ * Formalism.QuantumDeterminants.Hpk k r * x = xᴴ * (aᴴ * Formalism.QuantumDeterminants.Hpk k r * a) * x := by rw [ha']
    _ = (a * x)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * x) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.QuantumDeterminants.Hpk k r := hax'
end Formalism.FourierDecayAlt.P.DDSmoothness
