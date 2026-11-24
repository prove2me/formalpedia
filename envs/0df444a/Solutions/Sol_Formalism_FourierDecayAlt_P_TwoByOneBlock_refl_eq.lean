-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoByOneBlock.refl_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:46:39.429677+00:00
-- url     : https://prove2.me/submissions/5107bb12-4b1c-4bb9-b380-d1f5a6bc048f

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_cs_sq

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
theorem _root_.solution (n : ℕ) {T T' : ℝ} (hT : 0 < T) (hT' : 0 < T') (φ : ℂ → ℝ≥0∞) (y : ℂ) (s : ℝ) :
    (Ioi (0 : ℝ)).indicator (fun t => ENNReal.ofReal (t ^ n) * Ff T T' φ y (Complex.normSq y - t))
      (Complex.normSq y - s) = Rf n T T' φ y s := by
  have hTT : 0 < T * T' := mul_pos hT hT'
  rw [Set.indicator_apply, sub_sub_cancel]
  unfold Ff Rf
  by_cases hs : s ∈ Ioc 0 T'
  · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs]
    have hs0 : 0 < s := hs.1
    unfold Wf
    rw [Set.indicator_apply]
    have hN : Complex.normSq (cs T T' s * y) = T * T' / s * Complex.normSq y := by
      rw [Complex.normSq_mul, cs_sq hT hT' hs0]
    have hiff : (T * T' < Complex.normSq (cs T T' s * y)) ↔ 0 < Complex.normSq y - s := by
      rw [hN, div_mul_eq_mul_div, lt_div_iff₀ hs0, sub_pos]
      exact mul_lt_mul_iff_right₀ hTT
    by_cases h : 0 < Complex.normSq y - s
    · rw [if_pos (show Complex.normSq y - s ∈ Ioi (0 : ℝ) from h),
        if_pos (show cs T T' s * y ∈ {ζ : ℂ | T * T' < Complex.normSq ζ} from hiff.2 h), ← mul_assoc,
        ← ENNReal.ofReal_mul (by positivity), ← mul_pow, hN]
      congr 3
      field_simp
    · rw [if_neg (show ¬ Complex.normSq y - s ∈ Ioi (0 : ℝ) from h),
        if_neg (show ¬ cs T T' s * y ∈ {ζ : ℂ | T * T' < Complex.normSq ζ} from fun h' => h (hiff.1 h')), mul_zero]
  · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs, mul_zero, ite_self]
end Formalism.FourierDecayAlt.P.TwoByOneBlock
