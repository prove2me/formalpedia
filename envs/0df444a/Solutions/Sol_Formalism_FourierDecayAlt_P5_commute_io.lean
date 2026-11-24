-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.commute_io
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:46:34.760222+00:00
-- url     : https://prove2.me/submissions/87086bfc-8147-4a04-a8ed-7067911f1de8

import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaLevelZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMemMatrixAlgebra
import Theorems.Thm_Formalism_FourierDecayAlt_P5_mem_matSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T
variable {A : Type} [Ring A] [Algebra ℂ A]
variable {S : Type} [Fintype S] [DecidableEq S] (C : Subalgebra ℂ A)
namespace Formalism.FourierDecayAlt.P5
theorem _root_.solution {f : A} {M : SlopeTestRemainingChoices S A} (hM : M ∈ matSub (Subalgebra.centralizer ℂ {f}) (Ix S)) :
    Commute (io f : SlopeTestRemainingChoices S A) M := by
  have h : ∀ i j, f * M i j = M i j * f := by
    intro i j
    have hm := mem_matSub.1 hM i j
    rw [Subalgebra.mem_centralizer_iff] at hm
    exact hm f (Set.mem_singleton f)
  show (io f : SlopeTestRemainingChoices S A) * M = M * io f
  ext i j
  simp only [io, Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  exact h i j
end Formalism.FourierDecayAlt.P5
