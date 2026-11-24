-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qb1.qmF_reindex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:24:51.062899+00:00
-- url     : https://prove2.me/submissions/d69dabc8-4f10-4f03-8740-4909f2146662

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CasimirEigenvalueCoefficients

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.Qb1
variable {k r : ℕ} {Vs : Type} [NormedAddCommGroup Vs] [NormedSpace ℂ Vs]
variable {σ : Mx k r → (Vs →L[ℂ] Vs)}
namespace Formalism.FourierDecayAlt.P.Qb1
theorem _root_.solution {X : Type*} [AddCommGroup X] [Module ℂ X] {n : ℕ} (Eop : Fin n → Fin n → X → X) (u : ℂ) (x : X) :
    ∀ (t : ℕ) (h : t = n) (a : Fin t → Fin n), (∀ j, (a j).val = j.val) →
      qmF Eop a a u x = qmF Eop (id : Fin n → Fin n) id u x := by
  intro t h a ha
  subst h
  have : a = id := funext fun j => Fin.ext (ha j)
  subst this
  rfl
end Formalism.FourierDecayAlt.P.Qb1
