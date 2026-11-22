-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.integrable_cut_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:18:50.961809+00:00
-- url     : https://prove2.me/submissions/ef68d7ca-ffa8-4069-972c-dee288ed3434

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseEstimates

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite
open Formalism.FourierDecayAlt.G Matrix MeasureTheory Filter Topology
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite
theorem _root_.solution {β : ℂ} {m : ℕ} {F : XY m → V} (hF : Integrable F (muXY β m))
    {χ : (Fin (m + 1) → ℂ) → ℝ} (hχ : Continuous χ) {B : ℝ} (hB : ∀ x, |χ x| ≤ B) :
    Integrable (fun p : XY m => ((χ p.1 : ℝ) : ℂ) • F p) (muXY β m) := by
  have hc : Continuous (fun p : XY m => ((χ p.1 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (hχ.comp continuous_fst)
  refine (hF.norm.const_mul B).mono (hc.aestronglyMeasurable.smul hF.aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun p => ?_
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_norm]
  exact mul_le_mul_of_nonneg_right ((hB _).trans (le_abs_self _)) (norm_nonneg _)
end Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite
