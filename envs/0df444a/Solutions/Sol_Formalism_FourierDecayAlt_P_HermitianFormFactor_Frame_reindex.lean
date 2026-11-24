-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.Frame.reindex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:02:25.089801+00:00
-- url     : https://prove2.me/submissions/7cc54e4d-701b-439d-a75f-1977af89acc8

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
theorem _root_.solution {P' Q' : Type} [Fintype P'] [DecidableEq P'] [Fintype Q'] [DecidableEq Q']
    (F : Frame H Ep Em) (eP : P' ≃ P) (eQ : Q' ≃ Q) :
    Frame H (Ep.submatrix id eP) (Em.submatrix id eQ) where
  pp := by
    rw [Matrix.conjTranspose_submatrix, ← Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, F.pp]
    exact Matrix.submatrix_one_equiv eP
  mm := by
    rw [Matrix.conjTranspose_submatrix, ← Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, F.mm]
    exact Matrix.submatrix_one_equiv eQ
  pm := by
    rw [Matrix.conjTranspose_submatrix, ← Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, F.pm]
    rfl
  sum := by
    rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_mul_equiv]
    exact F.sum
  diff := by
    rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_mul_equiv]
    exact F.diff
end Formalism.FourierDecayAlt.P.HermitianFormFactor.Frame
