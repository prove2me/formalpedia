-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TInvW.conj_part
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:51:12.824339+00:00
-- url     : https://prove2.me/submissions/4312989f-116b-40e3-9078-24aab45cb985

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_TransferInvarianceRestriction
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_TransferInvarianceCongruence
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_hpk_inv
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_hpk_hh
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_uh_inv_eq
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_herm
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_sq


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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.TInvW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.QuantumDeterminants.GBasic Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.TInvW
theorem _root_.solution {s : Mx k r} (hs : s ∈ UH (Hpk k r)) (Z : Mx k r) :
    (Hpk k r)⁻¹ * (s⁻¹ * Z * s)ᴴ * Hpk k r = s⁻¹ * ((Hpk k r)⁻¹ * Zᴴ * Hpk k r) * s := by
  have hi := uh_inv_eq hs
  have h1 : sᴴ = Hpk k r * s⁻¹ * Hpk k r := by
    rw [hi]
    simp only [mul_assoc, hpk_hh, Hpk_sq, mul_one]
  have h2 : (s⁻¹)ᴴ = Hpk k r * s * Hpk k r := by
    rw [hi, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, Hpk_herm]
    simp only [mul_assoc]
  rw [hpk_inv, conjTranspose_mul, conjTranspose_mul, h2, h1]
  simp only [mul_assoc, hpk_hh, Hpk_sq, mul_one]
end Formalism.FourierDecayAlt.Q.TInvW
