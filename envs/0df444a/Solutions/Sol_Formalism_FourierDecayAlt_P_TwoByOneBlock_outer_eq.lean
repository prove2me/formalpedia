-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoByOneBlock.outer_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:50:49.582164+00:00
-- url     : https://prove2.me/submissions/cfdf8eff-d264-4cf7-a979-3c5ce2214a0e

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_cs_real_sq
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_Wf_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_lint_scale

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
theorem _root_.solution (n : ℕ) {T T' : ℝ} (hT : 0 < T) (hT' : 0 < T') {φ : ℂ → ℝ≥0∞} (hφ : Measurable φ) (s : ℝ) :
    (∫⁻ y : ℂ, Rf n T T' φ y s) =
      (Ioc 0 T').indicator (fun s => ENNReal.ofReal ((s / (T * T')) ^ n) * ENNReal.ofReal (s / (T * T'))) s *
        ∫⁻ ζ : ℂ, Wf n T T' φ ζ := by
  by_cases hs : s ∈ Ioc 0 T'
  · have hs0 : 0 < s := hs.1
    simp only [Rf, Set.indicator_of_mem hs]
    have hm : Measurable fun y : ℂ => Wf n T T' φ (cs T T' s * y) :=
      (Wf_meas n T T' hφ).comp (measurable_const_mul _)
    rw [lintegral_const_mul _ hm]
    have hne : -(√T * √(T' / s)) ≠ 0 :=
      neg_ne_zero.2 (mul_pos (Real.sqrt_pos.2 hT) (Real.sqrt_pos.2 (div_pos hT' hs0))).ne'
    unfold cs
    rw [lint_scale hne (Wf_meas n T T' hφ), cs_real_sq hT hT' hs0, inv_div, mul_assoc]
  · simp only [Rf, Set.indicator_of_notMem hs, lintegral_zero, zero_mul]
end Formalism.FourierDecayAlt.P.TwoByOneBlock
