-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux6.intRC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:55:17.90133+00:00
-- url     : https://prove2.me/submissions/bd22ee7b-1d73-479b-acf6-bb5df48b2032

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_isAddHaarMeasure_matrix_volume
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_finrank_RC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux6
namespace Formalism.FourierDecayAlt.P.Ux6
theorem _root_.solution (k j ρ : ℕ) (a : ℝ) (h : (((2 * ρ + k + 1) * (j * 2) + j * j * 2 + j : ℕ) : ℝ) < a) :
    Integrable (fun x : RC k j ρ => (1 + ‖x‖) ^ (-a)) (muRC k j ρ) := by
  have := isAddHaarMeasure_matrix_volume (2 * ρ + k + 1) j
  have : (volume : Measure ((Formalism.FourierDecayAlt.G.UT j → ℂ) × (Fin j → ℝ))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  have : (volume : Measure (RC k j ρ)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  unfold muRC
  refine integrable_one_add_norm (lt_of_le_of_lt ?_ h)
  exact_mod_cast finrank_RC k j ρ
end Formalism.FourierDecayAlt.P.Ux6
