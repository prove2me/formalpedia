-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.lattice_average_lemma_from_parts
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:01:32.538752+00:00
-- url     : https://prove2.me/submissions/fdd847fb-bd05-4e54-b871-7c8c75c5b556

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x6_first_level_of_equality

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open A5x6
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.A5.LemmaAAssemble := by
  unfold Formalism.FourierDecayAlt.A5.LemmaAAssemble Formalism.FourierDecayAlt.A5.LemmaA
  intro hA2 hPars hTh hA13 hStep hN0 hSup hBD
  refine ⟨hA2, ?_, hTh, hA13, hN0, hSup, hBD⟩
  intro s hs
  induction s, hs using Nat.le_induction with
  | base => exact first_level_of_equality hA13
  | succ s hs ih =>
    unfold Formalism.FourierDecayAlt.A5.A13 at ih ⊢
    intro K _ _ _ R ψ hLD hU
    unfold Formalism.FourierDecayAlt.A5.ThetaExistsStep at hStep
    exact hStep hA2 hPars K R ψ hLD hU s hs (ih K R ψ hLD hU)
end Formalism.FourierDecayAlt.P
