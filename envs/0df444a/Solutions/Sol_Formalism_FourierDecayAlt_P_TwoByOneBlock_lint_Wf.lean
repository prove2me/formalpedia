-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoByOneBlock.lint_Wf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:30:54.174488+00:00
-- url     : https://prove2.me/submissions/6019e632-db9c-46d1-9fa3-1b8302b88e42

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
theorem _root_.solution (n : ℕ) (T T' : ℝ) (φ : ℂ → ℝ≥0∞) :
    (∫⁻ ζ : ℂ, ENNReal.ofReal (zWeight (n + 1) T T' ζ) * φ ζ) = ∫⁻ ζ : ℂ, Wf n T T' φ ζ := by
  have hnull : volume {ζ : ℂ | Complex.normSq ζ = T * T'} = 0 := by
    refine measure_mono_null ?_ (Measure.addHaar_sphere volume (0 : ℂ) (√(T * T')))
    intro ζ (hζ : Complex.normSq ζ = T * T')
    rw [mem_sphere_zero_iff_norm, ← hζ, Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  refine lintegral_congr_ae ?_
  have : ∀ᵐ ζ : ℂ, ¬ Complex.normSq ζ = T * T' := by rw [ae_iff]; simpa using hnull
  filter_upwards [this] with ζ hζ
  unfold Wf zWeight
  rw [Set.indicator_apply]
  by_cases h : T * T' < Complex.normSq ζ
  · rw [if_pos h.le, if_pos (show ζ ∈ {ζ : ℂ | T * T' < Complex.normSq ζ} from h), Nat.add_sub_cancel]
  · rw [if_neg (fun h' => h (lt_of_le_of_ne h' (Ne.symm hζ))),
      if_neg (show ¬ ζ ∈ {ζ : ℂ | T * T' < Complex.normSq ζ} from h)]; simp
end Formalism.FourierDecayAlt.P.TwoByOneBlock
