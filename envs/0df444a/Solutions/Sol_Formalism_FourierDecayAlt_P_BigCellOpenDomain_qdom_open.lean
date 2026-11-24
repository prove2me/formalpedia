-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BigCellOpenDomain.qdom_open
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:13:01.711622+00:00
-- url     : https://prove2.me/submissions/436c51c2-266a-4432-a030-8b2dfd973beb

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordKeyIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellOpenDomain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BigCellOpenDomain
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
namespace Formalism.FourierDecayAlt.P.BigCellOpenDomain
theorem _root_.solution (z z' : Fin (2 * r + k + 1) → ℂ) : IsOpen (QDom k r z z') := by
  have h1 : IsOpen {q : (Fin r → ℂ) × ℂ | ∀ a, q.1 a ≠ 0} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun a =>
      isOpen_ne_fun ((continuous_apply a).comp continuous_fst) continuous_const
  have h2 : IsOpen {q : (Fin r → ℂ) × ℂ | Tz k r z * Tz k r z' < Complex.normSq q.2} :=
    isOpen_lt continuous_const (Complex.continuous_normSq.comp continuous_snd)
  exact h1.inter h2
end Formalism.FourierDecayAlt.P.BigCellOpenDomain
