-- Prove2me | solution 1 for Formalism.REAL.exp_log_of_pos_spectrum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:35:00.70983+00:00
-- url     : https://prove2.me/submissions/053a220a-43ec-43c7-b0cf-5c3a19ef8b76

import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IndefiniteUnitaryPreservesForm

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
theorem _root_.solution {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsSelfAdjoint P)
    (hs : ∀ x ∈ spectrum ℝ P, 0 < x) : NormedSpace.exp (CFC.log P) = P := by
  have hl : IsSelfAdjoint (CFC.log P) := cfc_predicate Real.log P
  refine Eq.trans (CFC.real_exp_eq_normedSpace_exp hl).symm ?_
  unfold CFC.log
  rw [← cfc_comp Real.exp Real.log P hP Real.continuous_exp.continuousOn
    (Real.continuousOn_log.mono fun x hx => (hs x hx).ne')]
  conv_rhs => rw [← cfc_id ℝ P hP]
  exact cfc_congr fun x hx => Real.exp_log (hs x hx)
end Formalism.REAL
