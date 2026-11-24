-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoByOneBlock.lint_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:30:56.253147+00:00
-- url     : https://prove2.me/submissions/1690ce31-111a-42f2-b83b-e9f035b1503c

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
theorem _root_.solution {a : ℝ} (ha : a ≠ 0) {g : ℂ → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ y : ℂ, g ((a : ℂ) * y)) = ENNReal.ofReal ((a ^ 2)⁻¹) * ∫⁻ ζ : ℂ, g ζ := by
  have h := Measure.map_addHaar_smul (volume : Measure ℂ) ha
  rw [Complex.finrank_real_complex, abs_of_nonneg (inv_nonneg.2 (sq_nonneg a))] at h
  have h2 : (∫⁻ y : ℂ, g (a • y)) = ∫⁻ ζ, g ζ ∂(Measure.map (a • ·) (volume : Measure ℂ)) :=
    (lintegral_map hg (measurable_const_smul a)).symm
  rw [h, lintegral_smul_measure] at h2
  simpa only [Complex.real_smul, smul_eq_mul] using h2
end Formalism.FourierDecayAlt.P.TwoByOneBlock
