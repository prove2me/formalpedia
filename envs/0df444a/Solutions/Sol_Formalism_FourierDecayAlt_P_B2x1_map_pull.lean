-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x1.map_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:21:14.22954+00:00
-- url     : https://prove2.me/submissions/e7a1e9f6-18c3-4699-8e10-7903b1f307a7

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BlochKatoDuality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x1_inc_memb
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x1_range_inc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x1
variable {k r : ℕ}
variable {U : Set (Mat k r)} {hU : IsClosedSubgroup U}
namespace Formalism.FourierDecayAlt.P.B2x1
theorem _root_.solution (μ : Measure (Mt k r)) (h : μ Uᶜ = 0) : (pull hU μ).map inc = μ := by
  rw [pull, inc_memb.map_comap, range_inc]
  exact Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact h)
end Formalism.FourierDecayAlt.P.B2x1
