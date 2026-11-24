-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.UH_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:55:41.015945+00:00
-- url     : https://prove2.me/submissions/dec0386e-5c69-4776-8874-326400da4e9b

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
  {H : Matrix m m ℂ} {Ep : Matrix m P ℂ} {Em : Matrix m Q ℂ}
attribute [local instance] isAddHaarMeasure_matrix_volume
attribute [local instance] haar_prod2
namespace Formalism.FourierDecayAlt.P.HermitianFormFactor
theorem _root_.solution (hH : IsUnit H.det) {g : Matrix m m ℂ} (hg : g ∈ UH H) : IsUnit g.det := by
  have h := congrArg Matrix.det (show gᴴ * H * g = H from hg)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at h
  rw [isUnit_iff_ne_zero]
  intro h0
  rw [h0, mul_zero] at h
  exact hH.ne_zero h.symm
end Formalism.FourierDecayAlt.P.HermitianFormFactor
