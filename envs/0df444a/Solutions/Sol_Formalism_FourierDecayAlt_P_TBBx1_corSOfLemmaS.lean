-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TBBx1.corSOfLemmaS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:38:45.174563+00:00
-- url     : https://prove2.me/submissions/11f3dc53-dbae-457d-a97c-03d7c913167b

import Definitions.Def_Formalism_HermitianCurvature_StatementTBB
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnIoiTruncatedPowerMoment
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MinLeTruncatedExponential
import Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx1_admissible_word_nil
import Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx1_corollary_s_induction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TBBx1
open Finset Filter Topology MeasureTheory Real
open Formalism.FourierDecayAlt.TBB
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
namespace Formalism.FourierDecayAlt.P.TBBx1
theorem _root_.solution : CorSOfLemmaS := by
  intro Wp Wq _ _ _ _ _ _ P p nn F Y Λ K N C₂ hN hC _ hL γ hγ
  exact corollary_s_induction p nn F Y Λ K N C₂ hC hL γ (P.r + 1) hγ le_rfl [] admissible_word_nil (by simpa using hN)
end Formalism.FourierDecayAlt.P.TBBx1
