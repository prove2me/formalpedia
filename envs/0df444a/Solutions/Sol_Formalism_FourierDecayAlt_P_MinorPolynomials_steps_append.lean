-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.MinorPolynomials.steps_append
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:47:26.143717+00:00
-- url     : https://prove2.me/submissions/b579bfbe-ae9f-421e-998a-53506451d34f

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenBigCellSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MemStepsFull

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
theorem _root_.solution (D : RealPlaceData k r Wp Wq) {nf : ℕ} (w : List (Mat k r)) (L₁ L₂ : FS k r nf) :
    steps D w (L₁ ++ L₂) = steps D w L₁ ++ steps D w L₂ := by
  induction w with
  | nil => rfl
  | cons X w ih =>
    show step D X (steps D w (L₁ ++ L₂)) = step D X (steps D w L₁) ++ step D X (steps D w L₂)
    rw [ih]
    simp [step, List.flatMap_append]
end Formalism.FourierDecayAlt.P.MinorPolynomials
