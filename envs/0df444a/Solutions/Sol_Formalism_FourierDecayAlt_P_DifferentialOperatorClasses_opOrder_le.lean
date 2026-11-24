-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DifferentialOperatorClasses.opOrder_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:16:59.873452+00:00
-- url     : https://prove2.me/submissions/2506c444-c88d-4fd7-9772-34e9713bee12

import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HomogeneityNaturalDegree
import Mathlib.Topology.Algebra.MvPolynomial
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellVanishingOfCommute

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Filter Topology
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DifferentialOperatorClasses
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.DifferentialOperatorClasses
theorem _root_.solution (D : B.RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → B.Mat k r → C6.EndH Wp Wq)
    (L : Finset (Fin (r + 2))) (o κ : ℕ) (Θ : B.DiffOp k r Wp Wq) (h : C6.InDDPlus D fib L o κ Θ) :
    B.opOrder Θ ≤ o := by
  have hw : ∀ T ∈ Θ, T.word.length ≤ o := fun T hT => by
    obtain ⟨P, a, b, c, es, hP, hab, hlen, hlie, hco⟩ := h.2.2 T hT
    omega
  unfold B.opOrder
  clear h
  induction Θ with
  | nil => simp
  | cons T Θ ih =>
    simp only [List.map_cons, List.foldr_cons]
    exact max_le (hw T (by simp)) (ih (fun T' hT' => hw T' (by simp [hT'])))
end Formalism.FourierDecayAlt.P.DifferentialOperatorClasses
