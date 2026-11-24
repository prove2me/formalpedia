-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.EabLie.hpart_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:43:54.994779+00:00
-- url     : https://prove2.me/submissions/f8126ff4-0bcf-449f-9b60-334be77c55de

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DerivativePreservation_HasDerivAtExt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DerivativePreservation_EabPresMain
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabLie_exp_hpart1_mem
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabLie_exp_hpart2_mem


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
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.Q.EabLie
theorem _root_.solution (i : Fin (r + 1)) (p q : Fin (mdim k r i)) :
    (∀ t : ℝ, NormedSpace.exp ((t : ℂ) •
      hpart1 (Hpk k r) (Matrix.single (posL k r i p) (posL k r i q) 1)) ∈ Glev k r i) ∧
    (∀ t : ℝ, NormedSpace.exp ((t : ℂ) •
      hpart2 (Hpk k r) (Matrix.single (posL k r i p) (posL k r i q) 1)) ∈ Glev k r i) :=
  ⟨exp_hpart1_mem i p q, exp_hpart2_mem i p q⟩
end Formalism.FourierDecayAlt.Q.EabLie
