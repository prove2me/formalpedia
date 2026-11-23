-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx1.dS_poly
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:55:04.607603+00:00
-- url     : https://prove2.me/submissions/7405df84-6ee8-44c9-9587-47d35c6e579f

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StepClaimFromStepsFull
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedL2ConstMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_iterDeriv_poly
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_mkP_coeff
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_mkP_eval


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
theorem _root_.solution (B : Base) {A A' : Type} (T : Fn B A → Fn B A') (u : Fn B A) (d : ℕ) (c : ℕ → Fn B A')
    (hc : ∀ (s : ℝ) ω a, conjS B T u s ω a = ∑ q ∈ range (d + 1), (s : ℂ) ^ q * c q ω a) (p : ℕ) (ω : B.Ω) (a : A') :
    dS B T u p ω a = p.factorial * (if p < d + 1 then c p ω a else 0) := by
  unfold dS
  have h : (fun s : ℝ => conjS B T u s ω a) = fun s : ℝ => (mkP d (fun q => c q ω a)).eval (s : ℂ) := by
    funext s; rw [hc, mkP_eval]
  rw [h, iterDeriv_poly]
  simp only [Complex.ofReal_zero]
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative, mkP_coeff]
  simp [Nat.descFactorial_self]
end Formalism.FourierDecayAlt.P.LEx1
