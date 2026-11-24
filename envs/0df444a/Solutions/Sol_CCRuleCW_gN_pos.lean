-- Prove2me | solution 1 for CCRuleCW.gN_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:00:34.24203+00:00
-- url     : https://prove2.me/submissions/cc1c3fa1-ff7a-4767-955e-d6ebcdf053aa

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_ExpIntertwine
import Theorems.Thm_CCRuleCW_one_le_gN

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate Nat
noncomputable section
open CCRuleCW
open Formalism.FourierDecayAlt
namespace CCRuleCW
theorem _root_.solution {k r : ℕ} (g : B.Mat k r) (hg : g ∈ B.GV k r) : 0 < B.gN g :=
  lt_of_lt_of_le one_pos (one_le_gN g hg)
end CCRuleCW
