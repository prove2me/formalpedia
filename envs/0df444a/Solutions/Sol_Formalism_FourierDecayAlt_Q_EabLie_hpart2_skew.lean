-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.EabLie.hpart2_skew
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:03:21.121847+00:00
-- url     : https://prove2.me/submissions/2bc8e3a1-e309-491d-ad63-4b4bdad7e1b4

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DerivativePreservation_HasDerivAtExt
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabLie_hpk_inv
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabLie_hpk_hh
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_Q_EabLie_hpk_hh__b7503cf64b36
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_herm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.EabLie
open Formalism.REAL Formalism.QuantumDeterminants Formalism.QuantumDeterminants.GBasic Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.EabLie
theorem _root_.solution (Z : Mx k r) :
    (hpart2 (Hpk k r) Z)ᴴ = -(Hpk k r * hpart2 (Hpk k r) Z * Hpk k r) := by
  unfold hpart2
  rw [hpk_inv]
  simp only [conjTranspose_smul, conjTranspose_add, conjTranspose_mul, Hpk_herm,
    conjTranspose_conjTranspose, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_assoc, hpk_hh]
  simp only [← Matrix.mul_assoc, hpk_hh']
  have : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I)) := by
    rw [star_div₀, star_one, star_mul', Complex.star_def, Complex.conj_I, map_ofNat]
    rw [mul_neg, div_neg]
  rw [this, neg_smul]
  exact congrArg (fun M : Mx k r => -((1 / (2 * Complex.I)) • M)) (add_comm _ _)
end Formalism.FourierDecayAlt.Q.EabLie
