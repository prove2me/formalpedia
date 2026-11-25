-- Prove2me | solution 1 for Formalism.L2.Th1.B.Cor.jets_of_odd_parallelogram_phi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:29:05.087492+00:00
-- url     : https://prove2.me/submissions/47fc4545-eb7f-4699-ae83-e2f13793fe54

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_SigmaOneCocycleShifted
import Theorems.Thm_Formalism_L2_Th1_B_Cor_first_jet_of_formal_law
import Theorems.Thm_Formalism_L2_Th1_B_f1O
import Theorems.Thm_Formalism_L2_Th1_B_jetsThree
import Theorems.Thm_Formalism_L2_Th1_B_phOEven


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Cor
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 swap2 DivAB)
namespace Formalism.L2.Th1.B.Cor
theorem _root_.solution : JetsPhO := by
  intro K _ _ _ g2 g3 s2 c0 P l i ep F hP hF hi hC h2 n hn
  rcases hn with rfl | hn
  · have hS := phOEven K s2 P l i hP.2.1 hF.2.2.1 hF.2.2.2.1 hi
    have h := first_jet_of_formal_law K l i _ hF.2.2.1 hF.2.2.2.1 hi hS
    rw [norm_mul, h2, one_mul] at h
    exact h
  · exact jetsThree K F l _ hF (f1O K g2 g3 s2 c0 P l i ep F hP hF hi hC h2).2.2.1 n hn
end Formalism.L2.Th1.B.Cor
