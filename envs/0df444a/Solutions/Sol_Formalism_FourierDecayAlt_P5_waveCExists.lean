-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.waveCExists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:05:19.307875+00:00
-- url     : https://prove2.me/submissions/e3d5c0dd-154e-4bc3-a0fa-006a9741f12e

import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaLevelZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermMulVecMulVec
import Theorems.Thm_Formalism_FourierDecayAlt_P5_mulOp_isMulOp
import Theorems.Thm_Formalism_FourierDecayAlt_P5_contDiff_fsv_coord

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate ComplexOrder ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P5
theorem _root_.solution : WaveCExists := by
  intro Wp Wq _ _ _ _ k r z z' π π' l s
  exact ⟨mulOp (π := π) (π' := π') (fun x => fsv s (x.1 l)) (contDiff_fsv_coord l s)
    (fun _ _ _ _ _ _ => rfl), mulOp_isMulOp _ _ _⟩
end Formalism.FourierDecayAlt.P5
