-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x3.fix_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:57:25.301315+00:00
-- url     : https://prove2.me/submissions/f22e5c12-3513-4d75-97e7-cf40961528a1

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x3
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x3
theorem _root_.solution {g : Mat k r} (hg : g ∈ GV k r) {f : Fin (2 * r + k + 1) → ℂ} (hf : g *ᵥ f = f) :
    gᴴ *ᵥ (Hpk k r *ᵥ f) = Hpk k r *ᵥ f := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  calc gᴴ *ᵥ (Hpk k r *ᵥ f) = gᴴ *ᵥ (Hpk k r *ᵥ (g *ᵥ f)) := by rw [hf]
    _ = (gᴴ * Hpk k r * g) *ᵥ f := by simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    _ = Hpk k r *ᵥ f := by rw [hg']
end Formalism.FourierDecayAlt.P.B2x3
