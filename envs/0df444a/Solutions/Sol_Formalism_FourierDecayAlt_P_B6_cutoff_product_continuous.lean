-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.cutoff_product_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:06:03.003463+00:00
-- url     : https://prove2.me/submissions/bb70091d-bd12-4a95-a240-1900f200d2e4

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P.B6
theorem _root_.solution {v1 v2 : ℝ → ℝ} (hv1 : Continuous v1) (hv2 : Continuous v2)
    (h1 : ∀ t, t ∉ Set.Ioo (1 / 2 : ℝ) 2 → v1 t = 0) (h2 : ∀ t, t ∉ Set.Ioo (1 / 2 : ℝ) 2 → v2 t = 0)
    {q : ℝ → ℝ → ℂ} (hq : ContinuousOn (fun t : ℝ × ℝ => q t.1 t.2) Quad) :
    Continuous (fun t : ℝ × ℝ => ((v1 t.1 * v2 t.2 : ℝ) : ℂ) * q t.1 t.2) := by
  have e : (fun t : ℝ × ℝ => ((v1 t.1 * v2 t.2 : ℝ) : ℂ) * q t.1 t.2) =
      fun t : ℝ × ℝ => ((v1 t.1 * v2 t.2 : ℝ) : ℂ) * q (max t.1 (1 / 2)) (max t.2 (1 / 2)) := by
    funext t
    by_cases ht1 : (1 / 2 : ℝ) ≤ t.1
    · by_cases ht2 : (1 / 2 : ℝ) ≤ t.2
      · rw [max_eq_left ht1, max_eq_left ht2]
      · rw [h2 t.2 (fun h => ht2 h.1.le)]; simp
    · rw [h1 t.1 (fun h => ht1 h.1.le)]; simp
  rw [e]
  have hc : Continuous fun t : ℝ × ℝ => ((max t.1 (1 / 2), max t.2 (1 / 2)) : ℝ × ℝ) :=
    (continuous_fst.max continuous_const).prodMk (continuous_snd.max continuous_const)
  have hm : ∀ t : ℝ × ℝ, ((max t.1 (1 / 2), max t.2 (1 / 2)) : ℝ × ℝ) ∈ Quad := fun t =>
    ⟨lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) (le_max_right _ _),
      lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) (le_max_right _ _)⟩
  exact (Complex.continuous_ofReal.comp ((hv1.comp continuous_fst).mul (hv2.comp continuous_snd))).mul
    (hq.comp_continuous hc hm)
end Formalism.FourierDecayAlt.P.B6
