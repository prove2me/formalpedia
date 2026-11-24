-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoByOneBlock.Jc_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:29:15.746308+00:00
-- url     : https://prove2.me/submissions/901c83d6-86cf-4699-9f17-9c19fbc96834

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
theorem _root_.solution (n : ℕ) {T T' : ℝ} (hT : 0 < T) (hT' : 0 < T') : Jc n T T' ≠ ∞ := by
  unfold Jc
  have hb : ∀ s ∈ Ioc 0 T', ENNReal.ofReal ((s / (T * T')) ^ n) * ENNReal.ofReal (s / (T * T')) ≤
      ENNReal.ofReal ((1 / T) ^ n) * ENNReal.ofReal (1 / T) := by
    intro s hs
    have h1 : s / (T * T') ≤ 1 / T := by
      rw [div_le_div_iff₀ (by positivity) hT]; nlinarith [hs.2]
    have h0 : 0 ≤ s / (T * T') := by have := hs.1; positivity
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ h0 h1 n)) (ENNReal.ofReal_le_ofReal h1)
  refine ne_top_of_le_ne_top ?_ (setLIntegral_mono' measurableSet_Ioc hb)
  rw [setLIntegral_const, Real.volume_Ioc]
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top
end Formalism.FourierDecayAlt.P.TwoByOneBlock
