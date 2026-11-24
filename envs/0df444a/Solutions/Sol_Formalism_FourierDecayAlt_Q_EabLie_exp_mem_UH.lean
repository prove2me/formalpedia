-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.EabLie.exp_mem_UH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:12:53.022158+00:00
-- url     : https://prove2.me/submissions/75911145-8f84-4c6e-b0cf-13a9e1bdd5a8

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DerivativePreservation_HasDerivAtExt
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabLie_hpk_inv
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabLie_hpk_unit
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_sq


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
theorem _root_.solution (Y : Mx k r) (hY : Yᴴ = -(Hpk k r * Y * Hpk k r)) :
    NormedSpace.exp Y ∈ UH (Hpk k r) := by
  have hYh : Yᴴ = Hpk k r * (-Y) * (Hpk k r)⁻¹ := by
    rw [hY, hpk_inv, Matrix.mul_neg, Matrix.neg_mul]
  have hexp : (NormedSpace.exp Y)ᴴ = Hpk k r * NormedSpace.exp (-Y) * Hpk k r := by
    rw [← Matrix.exp_conjTranspose, hYh, Matrix.exp_conj _ _ hpk_unit, hpk_inv]
  have hc : NormedSpace.exp (-Y) * NormedSpace.exp Y = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl Y)), neg_add_cancel,
      NormedSpace.exp_zero]
  show (NormedSpace.exp Y)ᴴ * Hpk k r * NormedSpace.exp Y = Hpk k r
  rw [hexp, Matrix.mul_assoc (Hpk k r * NormedSpace.exp (-Y)) (Hpk k r) (Hpk k r), Hpk_sq,
    Matrix.mul_one, Matrix.mul_assoc, hc, Matrix.mul_one]
end Formalism.FourierDecayAlt.Q.EabLie
