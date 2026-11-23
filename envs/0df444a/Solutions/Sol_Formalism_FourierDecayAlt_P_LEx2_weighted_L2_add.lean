-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.weighted_L2_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:25:55.757378+00:00
-- url     : https://prove2.me/submissions/e4c067fa-5090-4884-8015-06d7418d97be

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MeasIterDeriv
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThetaLimit
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedL2BoundedMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P.LEx2
theorem _root_.solution (B : Base) (wt : B.Ω → ℝ) (hw : ∀ ω, 0 ≤ wt ω) (f g : B.Ω → ℂ) (hf : WeightedL2 B wt f)
    (hg : WeightedL2 B wt g) : WeightedL2 B wt (fun ω => f ω + g ω) := by
  refine ⟨hf.1.add hg.1, ?_⟩
  have hcross : AEStronglyMeasurable
      (fun ω => ((wt ω * ‖f ω‖ ^ 2 : ℝ) : ℂ) * conj (g ω) / conj (f ω)) B.μ := by
    have h1 : AEMeasurable (fun ω => ((wt ω * ‖f ω‖ ^ 2 : ℝ) : ℂ)) B.μ :=
      Complex.measurable_ofReal.comp_aemeasurable hf.2.1.aemeasurable
    have h2 : AEMeasurable (fun ω => conj (g ω)) B.μ :=
      (Complex.continuous_conj.measurable).comp_aemeasurable hg.1.aemeasurable
    have h3 : AEMeasurable (fun ω => conj (f ω)) B.μ :=
      (Complex.continuous_conj.measurable).comp_aemeasurable hf.1.aemeasurable
    exact ((h1.mul h2).div h3).aestronglyMeasurable
  have heq : (fun ω => wt ω * ‖f ω + g ω‖ ^ 2) = fun ω => wt ω * ‖f ω‖ ^ 2 + wt ω * ‖g ω‖ ^ 2 +
      2 * (((wt ω * ‖f ω‖ ^ 2 : ℝ) : ℂ) * conj (g ω) / conj (f ω)).re := by
    funext ω
    by_cases h0 : f ω = 0
    · simp [h0]
    · have hc : conj (f ω) ≠ 0 := by simpa using h0
      have h1 : ((wt ω * ‖f ω‖ ^ 2 : ℝ) : ℂ) * conj (g ω) / conj (f ω) = (wt ω : ℂ) * (f ω * conj (g ω)) := by
        rw [div_eq_iff hc]
        push_cast
        rw [← Complex.mul_conj']
        ring
      rw [h1, Complex.re_ofReal_mul, Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_add]
      ring
  have hmeas : AEStronglyMeasurable (fun ω => wt ω * ‖f ω + g ω‖ ^ 2) B.μ := by
    rw [heq]
    exact (hf.2.1.add hg.2.1).add ((Complex.continuous_re.comp_aestronglyMeasurable hcross).const_mul 2)
  refine Integrable.mono' ((hf.2.const_mul 2).add (hg.2.const_mul 2)) hmeas (Filter.Eventually.of_forall ?_)
  intro ω
  have h1 : ‖f ω + g ω‖ ≤ ‖f ω‖ + ‖g ω‖ := norm_add_le _ _
  have h2 : ‖f ω + g ω‖ ^ 2 ≤ 2 * ‖f ω‖ ^ 2 + 2 * ‖g ω‖ ^ 2 := by
    nlinarith [norm_nonneg (f ω + g ω), norm_nonneg (f ω), norm_nonneg (g ω), sq_nonneg (‖f ω‖ - ‖g ω‖)]
  rw [Real.norm_of_nonneg (mul_nonneg (hw ω) (by positivity))]
  simp only [Pi.add_apply]
  nlinarith [hw ω, mul_le_mul_of_nonneg_left h2 (hw ω)]
end Formalism.FourierDecayAlt.P.LEx2
