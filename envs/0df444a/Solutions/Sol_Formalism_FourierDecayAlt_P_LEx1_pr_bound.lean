-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx1.pr_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:28:27.406865+00:00
-- url     : https://prove2.me/submissions/4a8addbb-5c4b-41c1-b20d-d84abf3e6643

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaEprimeFromSteps
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_amgm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx1
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P.LEx1
theorem _root_.solution (B : Base) {A : Type} [Fintype A] (wt : B.Ω → A → ℝ) (hpos : ∀ ω a, 0 ≤ wt ω a) (a b : Fn B A)
    (δ : ℝ) (hδ : 0 < δ) (ω : B.Ω) : ‖pr B wt a b ω‖ ≤ (LE.sq B wt a ω / δ + δ * LE.sq B wt b ω) / 2 := by
  unfold pr LE.sq
  rw [Finset.sum_div, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul, norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hpos ω i)]
  have := mul_le_mul_of_nonneg_left (amgm ‖a ω i‖ ‖b ω i‖ δ hδ) (hpos ω i)
  calc _ = wt ω i * (‖a ω i‖ * ‖b ω i‖) := by ring
    _ ≤ _ := this
    _ = _ := by ring
end Formalism.FourierDecayAlt.P.LEx1
