-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.MinorPolynomials.opOrder_le_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:23:22.618975+00:00
-- url     : https://prove2.me/submissions/48bb27cf-d660-4655-b7de-84cb7c21db0b

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ListMapSumApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ComposeDifferentialOperators

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial Set
open scoped ComplexConjugate ContDiff Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.MinorPolynomials
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryGroupMassFormula.UsCompose
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.MinorPolynomials
theorem _root_.solution (Θ : DiffOp k r Wp Wq) {n : ℕ} (h : ∀ T ∈ Θ, T.word.length ≤ n) : opOrder Θ ≤ n := by
  unfold opOrder
  induction Θ with
  | nil => simp
  | cons T t ih =>
    simp only [List.map_cons, List.foldr_cons]
    exact max_le (h T (by simp)) (ih fun T' hT' => h T' (by simp [hT']))
end Formalism.FourierDecayAlt.P.MinorPolynomials
