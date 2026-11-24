-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.qf_orbit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:29:21.854439+00:00
-- url     : https://prove2.me/submissions/528ef4bc-2f8a-4090-a2e8-17ecdbfcd299

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_Tm_mul_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_Tm_Em_mul

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
theorem _root_.solution (F : Frame H Ep Em) {g : Matrix m m ℂ} {a : Matrix Q Q ℂ} (hg : g ∈ UH H) (ha : IsUnit a.det) :
    qf (Tm H (g * Em * a)) (Epᴴ * (g * Em * a)) = bet Ep Em g := by
  have hT : Tm H (g * Em * a) = aᴴ * a := by
    rw [Matrix.mul_assoc, Tm_mul_left hg, Tm_Em_mul F]
  have ha' : IsUnit aᴴ.det := by
    rw [Matrix.det_conjTranspose]; exact ha.star
  rw [hT]
  unfold qf bet
  rw [Matrix.mul_inv_rev]
  congr 2
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul_cancel_left _ _ ha', Matrix.mul_nonsing_inv_cancel_left _ _ ha]
end Formalism.FourierDecayAlt.P.HermitianFormFactor
