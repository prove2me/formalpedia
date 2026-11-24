-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.Frame.Ep_H
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:19:47.598591+00:00
-- url     : https://prove2.me/submissions/65675f1a-feab-462f-be38-eba27f91f617

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_Frame_herm
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_Frame_H_Ep

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
theorem _root_.solution (F : Frame H Ep Em) : Epᴴ * H = Epᴴ := by
  have h := congrArg Matrix.conjTranspose F.H_Ep
  rwa [Matrix.conjTranspose_mul, F.herm] at h
end Formalism.FourierDecayAlt.P.HermitianFormFactor.Frame
