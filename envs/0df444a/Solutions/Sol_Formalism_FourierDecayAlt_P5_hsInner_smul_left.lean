-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.hsInner_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:36:38.273921+00:00
-- url     : https://prove2.me/submissions/c3cac7cc-d8cc-4c36-a933-b62272b1e070

import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaLevelZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMemMatrixAlgebra

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
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P5
theorem _root_.solution (a : ℂ) (U V : Wq →L[ℂ] Wp) : B.hsInner (a • U) V = a * B.hsInner U V := by
  have e : Formalism.FourierDecayAlt.B.hsVec (a • U) = a • Formalism.FourierDecayAlt.B.hsVec U := by
    unfold Formalism.FourierDecayAlt.B.hsVec
    rw [← WithLp.toLp_smul]
    first
      | rfl
      | (congr 1; funext i; simp)
  unfold Formalism.FourierDecayAlt.B.hsInner
  rw [e, inner_smul_right]
end Formalism.FourierDecayAlt.P5
