-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.Frame.card_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:36:39.729261+00:00
-- url     : https://prove2.me/submissions/8aee87ce-fe2e-4bbe-b9c0-536c5ee097e4

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormFactor
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {m P Q : Type} [Fintype m] [DecidableEq m] [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
variable {H : Matrix m m ℂ} {Ep : Matrix m P ℂ} {Em : Matrix m Q ℂ}
open Formalism.FourierDecayAlt.P.HermitianFormFactor.Frame
namespace Formalism.FourierDecayAlt.P.HermitianFormFactor.Frame
theorem _root_.solution (F : Frame H Ep Em) : (Fintype.card P : ℂ) + Fintype.card Q = Fintype.card m := by
  have h := congrArg Matrix.trace F.sum
  rw [Matrix.trace_add, Matrix.trace_mul_comm Ep, Matrix.trace_mul_comm Em, F.pp, F.mm] at h
  simpa using h
end Formalism.FourierDecayAlt.P.HermitianFormFactor.Frame
