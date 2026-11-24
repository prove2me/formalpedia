-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.Tm_Em_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:10:52.805805+00:00
-- url     : https://prove2.me/submissions/55770112-7bc2-42b1-b5c4-d7c1b91e3cf7

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_Frame_Em_H

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
theorem _root_.solution (F : Frame H Ep Em) (a : Matrix Q Q ℂ) : Tm H (Em * a) = aᴴ * a := by
  have h : (Em * a)ᴴ * H * (Em * a) = -(aᴴ * a) := by
    rw [Matrix.conjTranspose_mul, show aᴴ * Emᴴ * H * (Em * a) = aᴴ * ((Emᴴ * H) * Em) * a by
      simp only [Matrix.mul_assoc], F.Em_H, Matrix.neg_mul, F.mm, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_one]
  unfold Tm
  rw [h, neg_neg]
end Formalism.FourierDecayAlt.P.HermitianFormFactor
