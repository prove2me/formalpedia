-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoByOneBlock.cs_real_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:36:31.452496+00:00
-- url     : https://prove2.me/submissions/32ab44c5-73a6-4fe8-a57a-3d003523b47a

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TwoByOneBlock
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open Set
open scoped Pointwise
namespace Formalism.FourierDecayAlt.P.TwoByOneBlock
theorem _root_.solution {T T' s : ℝ} (hT : 0 < T) (hT' : 0 < T') (hs : 0 < s) :
    (-(√T * √(T' / s))) ^ 2 = T * T' / s := by
  calc (-(√T * √(T' / s))) ^ 2 = (√T) ^ 2 * (√(T' / s)) ^ 2 := by ring
    _ = T * (T' / s) := by rw [Real.sq_sqrt hT.le, Real.sq_sqrt (div_pos hT' hs).le]
    _ = T * T' / s := by ring
end Formalism.FourierDecayAlt.P.TwoByOneBlock
