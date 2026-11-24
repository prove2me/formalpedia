-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.UH_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:55:52.892107+00:00
-- url     : https://prove2.me/submissions/11ccfb46-281c-4e04-9194-a155324e1858

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
theorem _root_.solution {g h : Matrix m m ℂ} (hg : g ∈ UH H) (hh : h ∈ UH H) : g * h ∈ UH H := by
  show (g * h)ᴴ * H * (g * h) = H
  rw [Matrix.conjTranspose_mul, show hᴴ * gᴴ * H * (g * h) = hᴴ * (gᴴ * H * g) * h by
    simp only [Matrix.mul_assoc], show gᴴ * H * g = H from hg]
  exact hh
end Formalism.FourierDecayAlt.P.HermitianFormFactor
