-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.Tm_mul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:39:29.396747+00:00
-- url     : https://prove2.me/submissions/58808f48-e079-4c5e-8520-b786497f8aa3

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
namespace Formalism.FourierDecayAlt.P.HermitianFormFactor
theorem _root_.solution {g : Matrix m m ℂ} (hg : g ∈ UH H) (Y : Matrix m Q ℂ) : Tm H (g * Y) = Tm H Y := by
  have hg' : gᴴ * H * g = H := hg
  unfold Tm
  rw [Matrix.conjTranspose_mul, show Yᴴ * gᴴ * H * (g * Y) = Yᴴ * (gᴴ * H * g) * Y by
    simp only [Matrix.mul_assoc], hg']
end Formalism.FourierDecayAlt.P.HermitianFormFactor
