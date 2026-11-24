-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.mul_H_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:19:46.437555+00:00
-- url     : https://prove2.me/submissions/3186b7e6-1914-4786-bb29-509960e6f737

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_Frame_mp

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
theorem _root_.solution {g : Matrix m m ℂ} (h2 : H * H = 1) (hg : g ∈ UH H) : g * H * gᴴ = H := by
  have h1 : (H * gᴴ * H) * g = 1 := by
    rw [show H * gᴴ * H * g = H * (gᴴ * H * g) by simp only [Matrix.mul_assoc], show gᴴ * H * g = H from hg, h2]
  have h3 : g * (H * gᴴ * H) = 1 := by
    first
    | exact Matrix.mul_eq_one_comm.mp h1
    | exact mul_eq_one_comm.mp h1
    | rw [← Matrix.inv_eq_left_inv h1]; exact Matrix.mul_nonsing_inv _ (Matrix.isUnit_det_of_left_inverse h1)
  calc g * H * gᴴ = g * H * gᴴ * (H * H) := by rw [h2, Matrix.mul_one]
    _ = g * (H * gᴴ * H) * H := by simp only [Matrix.mul_assoc]
    _ = H := by rw [h3, Matrix.one_mul]
end Formalism.FourierDecayAlt.P.HermitianFormFactor
