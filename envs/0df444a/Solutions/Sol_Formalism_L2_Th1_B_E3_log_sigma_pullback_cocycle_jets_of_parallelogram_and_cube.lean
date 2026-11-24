-- Prove2me | solution 1 for Formalism.L2.Th1.B.E3.log_sigma_pullback_cocycle_jets_of_parallelogram_and_cube
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:04:13.44451+00:00
-- url     : https://prove2.me/submissions/cc76e0d3-b4d0-46a8-bddc-be71cca0adfc

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_FirstLevelOfThreeVarParallelogram
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_equivalence_rules
import Theorems.Thm_Formalism_L2_Th1_B_cobRules
import Theorems.Thm_Formalism_L2_Th1_B_constantCoeff_eq_zero_of_parallelogram
import Theorems.Thm_Formalism_L2_Th1_B_jetsThree
import Theorems.Thm_Formalism_L2_Th1_B_parO


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.E3
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 in3 swap2 DivAB equivalence_rules)
namespace Formalism.L2.Th1.B.E3
theorem _root_.solution (hP : ParThree) (hC : CubeFromPars) : LogSigmaPullbackCocycleJets := by
  intro K _ _ _ g2 g3 s2 c0 a1 a3 P l i ep F hW hF hi hc hc3
  have hpar := parO K g2 g3 s2 c0 P l i ep F hW hF hi hc
  have hp3 := hP K g2 g3 s2 c0 a1 a3 P l i ep F hW hF hi hc hc3
  have hd := hC K F l i (phO s2 P l) hF hi hpar hp3
  have hf0 := constantCoeff_eq_zero_of_parallelogram hF hi hpar
  obtain ⟨hdiv, hsw⟩ := cobRules K F l (phO s2 P l) hF hf0
  refine ⟨hdiv, hsw, hd, ?_, fun n hn => jetsThree K F l _ hF hd n hn⟩
  rw [hsw]
  exact hd
end Formalism.L2.Th1.B.E3
