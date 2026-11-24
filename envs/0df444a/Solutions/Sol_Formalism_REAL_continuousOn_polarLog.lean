-- Prove2me | solution 1 for Formalism.REAL.continuousOn_polarLog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:59:10.846818+00:00
-- url     : https://prove2.me/submissions/efc2d7c7-c3ff-48cb-a6b0-b23d4f4889cc

import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IndefiniteUnitaryPreservesForm
import Theorems.Thm_Formalism_REAL_conjTranspose_mul_self_pos_facts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder
noncomputable section
open Formalism Formalism.REAL
variable {n : ℕ}
namespace Formalism.REAL
theorem _root_.solution (ε : Fin n → Bool) : ContinuousOn (polarLog (n := n)) {g | inUJ ε g} := by
  have hc : ContinuousOn (fun g : Matrix (Fin n) (Fin n) ℂ => gᴴ * g) {g | inUJ ε g} :=
    (continuous_star.mul continuous_id).continuousOn
  have hlog : ContinuousOn (fun g : Matrix (Fin n) (Fin n) ℂ => CFC.log (gᴴ * g)) {g | inUJ ε g} :=
    CFC.continuousOn_log.comp hc (fun g hg => by
      show IsSelfAdjoint (gᴴ * g) ∧ IsUnit (gᴴ * g)
      exact ⟨(conjTranspose_mul_self_pos_facts hg).1, (conjTranspose_mul_self_pos_facts hg).2.1⟩)
  exact hlog.const_smul (1 / 2 : ℝ)
end Formalism.REAL
