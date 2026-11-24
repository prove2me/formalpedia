-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x1.pull_fin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:21:17.622051+00:00
-- url     : https://prove2.me/submissions/8a0a5018-b584-4314-ab89-542455157cc9

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BlochKatoDuality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x1_inc_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x1_inc_memb

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
theorem _root_.solution (μ : Measure (Mt k r)) (h : ∀ K : Set (Mt k r), IsCompact K → μ K < ∞) :
    IsFiniteMeasureOnCompacts (pull hU μ) := by
  refine ⟨fun K hK => ?_⟩
  rw [pull, inc_memb.comap_apply]
  exact h _ (hK.image inc_cont)
end Formalism.FourierDecayAlt.P.B2x1
