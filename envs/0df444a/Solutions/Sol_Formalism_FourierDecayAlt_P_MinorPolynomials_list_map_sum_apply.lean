-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.MinorPolynomials.list_map_sum_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:08:39.48763+00:00
-- url     : https://prove2.me/submissions/98bdfff3-d2b6-4c7c-a9a2-8c81fdb89c85

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MemStepsFull
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ListMapSumApply

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
theorem _root_.solution {α : Type*} (L : List α) (A : C6.EndH Wp Wq) (f : α → (Wq →L[ℂ] Wp)) :
    A (L.map f).sum = (L.map fun a => A (f a)).sum := by
  rw [map_list_sum, List.map_map]
  rfl
end Formalism.FourierDecayAlt.P.MinorPolynomials
