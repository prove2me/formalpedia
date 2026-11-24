-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x3.sand_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:35:55.1508+00:00
-- url     : https://prove2.me/submissions/e4e3a71d-c007-4814-8441-54a312b7e541

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_EmT_Em

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
theorem _root_.solution {a b : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (h : Em k r * a * (Em k r)ᵀ = Em k r * b * (Em k r)ᵀ) :
    a = b := by
  have h2 : (Em k r)ᵀ * (Em k r * a * (Em k r)ᵀ) * Em k r = (Em k r)ᵀ * (Em k r * b * (Em k r)ᵀ) * Em k r := by rw [h]
  have e : ∀ c : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, (Em k r)ᵀ * (Em k r * c * (Em k r)ᵀ) * Em k r = c := by
    intro c
    calc (Em k r)ᵀ * (Em k r * c * (Em k r)ᵀ) * Em k r = ((Em k r)ᵀ * Em k r) * c * ((Em k r)ᵀ * Em k r) := by
          simp only [Matrix.mul_assoc]
      _ = c := by rw [EmT_Em, Matrix.one_mul, Matrix.mul_one]
  rwa [e, e] at h2
end Formalism.FourierDecayAlt.P.B2x3
