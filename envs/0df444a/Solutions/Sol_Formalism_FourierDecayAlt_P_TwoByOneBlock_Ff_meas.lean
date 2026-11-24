-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoByOneBlock.Ff_meas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:57:37.2214+00:00
-- url     : https://prove2.me/submissions/d636fa95-23bb-43dc-b058-1a15e7102912

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_cs_meas

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
theorem _root_.solution (T T' : ℝ) {φ : ℂ → ℝ≥0∞} (hφ : Measurable φ) :
    Measurable fun p : ℂ × ℝ => Ff T T' φ p.1 p.2 := by
  have : (fun p : ℂ × ℝ => Ff T T' φ p.1 p.2) =
      (Prod.snd ⁻¹' Ioc 0 T').indicator fun p : ℂ × ℝ => φ (cs T T' p.2 * p.1) := by
    funext p
    by_cases h : p.2 ∈ Ioc 0 T'
    · rw [Ff, Set.indicator_of_mem h, Set.indicator_of_mem (show p ∈ Prod.snd ⁻¹' Ioc 0 T' from h)]
    · rw [Ff, Set.indicator_of_notMem h, Set.indicator_of_notMem (show ¬ p ∈ Prod.snd ⁻¹' Ioc 0 T' from h)]
  rw [this]
  exact (hφ.comp (((cs_meas T T').comp measurable_snd).mul measurable_fst)).indicator (measurable_snd measurableSet_Ioc)
end Formalism.FourierDecayAlt.P.TwoByOneBlock
