-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx2.hpart1_lie
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:54:53.893008+00:00
-- url     : https://prove2.me/submissions/bdacaab6-b598-4a7e-a439-12a2e4c9637c

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Qx2_hpk_sq__e1ad91698796
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_hpk_h
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_hpk_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.Qx2
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.Qx2
theorem _root_.solution (Z : Mx k r) :
    (hpart1 (Hpk k r) Z)ᴴ * Hpk k r + Hpk k r * hpart1 (Hpk k r) Z = 0 := by
  have hH : (Hpk k r)ᴴ = Hpk k r := hpk_h
  have hS' : ∀ X : Mx k r, Hpk k r * (Hpk k r * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hpk_sq', Matrix.one_mul]
  have hc : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [hpart1, hpk_inv, Matrix.conjTranspose_smul, hc, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hH]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, hpk_sq', hS',
    Matrix.mul_one]
  module
end Formalism.FourierDecayAlt.P.Qx2
