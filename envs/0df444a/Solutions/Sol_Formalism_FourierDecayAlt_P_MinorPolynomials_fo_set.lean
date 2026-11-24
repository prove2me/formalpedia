-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.MinorPolynomials.fo_set
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:47:53.694444+00:00
-- url     : https://prove2.me/submissions/6a0dda24-3d5d-4bff-b349-b753ade7e3d7

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
theorem _root_.solution {nf : ℕ} (X : Mat k r) :
    ∀ (es : List (Fin nf × List (Mat k r))) (i : Fin es.length),
      fo (es.set i ((es.get i).1, X :: (es.get i).2)) = fo es + 1 := by
  intro es
  induction es with
  | nil => intro i; exact i.elim0
  | cons e es ih =>
    intro i
    rcases i with ⟨_ | j, hj⟩
    · simp [fo]
      omega
    · have hj' : j < es.length := by simpa using hj
      have := ih ⟨j, hj'⟩
      have e2 : (e :: es).set (j + 1) (((e :: es).get ⟨j + 1, hj⟩).1, X :: ((e :: es).get ⟨j + 1, hj⟩).2) =
          e :: es.set j ((es.get ⟨j, hj'⟩).1, X :: (es.get ⟨j, hj'⟩).2) := rfl
      show fo ((e :: es).set (j + 1) (((e :: es).get ⟨j + 1, hj⟩).1, X :: ((e :: es).get ⟨j + 1, hj⟩).2)) =
        fo (e :: es) + 1
      rw [e2]
      simp only [fo, List.map_cons, List.sum_cons] at this ⊢
      omega
end Formalism.FourierDecayAlt.P.MinorPolynomials
