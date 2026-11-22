-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx1.iterDeriv_poly
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:03:00.795803+00:00
-- url     : https://prove2.me/submissions/65975016-597a-4636-9889-61bc1e0fb72a

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaEprimeFromSteps

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
open Polynomial
namespace Formalism.FourierDecayAlt.P.LEx1
theorem _root_.solution (P : ℂ[X]) (p : ℕ) :
    iteratedDeriv p (fun s : ℝ => P.eval (s : ℂ)) = fun s : ℝ => ((derivative^[p]) P).eval (s : ℂ) := by
  induction p generalizing P with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ']
    have : deriv (fun s : ℝ => P.eval (s : ℂ)) = fun s : ℝ => (derivative P).eval (s : ℂ) := by
      funext s
      exact ((P.hasDerivAt (s : ℂ)).comp_ofReal).deriv
    rw [this, ih]
    simp [Function.iterate_succ]
end Formalism.FourierDecayAlt.P.LEx1
