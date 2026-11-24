-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoByOneBlock.Jc_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:27:42.603114+00:00
-- url     : https://prove2.me/submissions/fea087b5-58be-498c-83d8-2def299e48d4

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
theorem _root_.solution (n : ℕ) {T T' : ℝ} (hT : 0 < T) (hT' : 0 < T') : Jc n T T' ≠ 0 := by
  unfold Jc
  have hm : Measurable fun s : ℝ => ENNReal.ofReal ((s / (T * T')) ^ n) * ENNReal.ofReal (s / (T * T')) :=
    (ENNReal.measurable_ofReal.comp ((measurable_id.div_const _).pow_const _)).mul
      (ENNReal.measurable_ofReal.comp (measurable_id.div_const _))
  refine ((setLIntegral_pos_iff hm).2 ?_).ne'
  have hsub : Ioc 0 T' ⊆ (Function.support fun s : ℝ =>
      ENNReal.ofReal ((s / (T * T')) ^ n) * ENNReal.ofReal (s / (T * T'))) ∩ Ioc 0 T' := by
    intro s hs
    refine ⟨?_, hs⟩
    have h0 : 0 < s / (T * T') := by have := hs.1; positivity
    rw [Function.mem_support]
    exact mul_ne_zero (ENNReal.ofReal_pos.2 (pow_pos h0 n)).ne' (ENNReal.ofReal_pos.2 h0).ne'
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [Real.volume_Ioc, sub_zero]
  exact ENNReal.ofReal_pos.2 hT'
end Formalism.FourierDecayAlt.P.TwoByOneBlock
