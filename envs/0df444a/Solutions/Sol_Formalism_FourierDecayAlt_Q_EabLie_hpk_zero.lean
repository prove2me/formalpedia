-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.EabLie.hpk_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:49:30.17005+00:00
-- url     : https://prove2.me/submissions/c8e92462-f6f8-4707-bf28-0b36b49ed60c

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DerivativePreservation_HasDerivAtExt

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
theorem _root_.solution (i : Fin (r + 1)) (p : Fin (mdim k r i)) (a : Fin r) (ha : a.val < i.val) :
    Hpk k r (posL k r i p) (eI k r a) = 0 ∧ Hpk k r (posL k r i p) (esI k r a) = 0 := by
  have hp := p.isLt
  have hi := i.isLt
  unfold mdim at hp
  constructor
  · simp only [Hpk, posL, eI, Fin.ext_iff]
    split_ifs <;> first | rfl | omega
  · simp only [Hpk, posL, esI, Fin.ext_iff]
    split_ifs <;> first | rfl | omega
end Formalism.FourierDecayAlt.Q.EabLie
