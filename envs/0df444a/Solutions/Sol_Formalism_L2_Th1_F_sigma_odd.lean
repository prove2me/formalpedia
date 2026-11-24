-- Prove2me | solution 1 for Formalism.L2.Th1.F.sigma_odd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:36:42.064204+00:00
-- url     : https://prove2.me/submissions/ed21f045-d626-4801-9377-802710664b0e

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Legendre
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaBasic
import Theorems.Thm_Formalism_L2_Th1_F_SigmaBasic_wFactor_neg_neg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Filter
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open SigmaBasic
namespace Formalism.L2.Th1.F
theorem _root_.solution : SigmaOdd := by
  intro L z
  have hP : ∏' l : L.lattice, wFactor (l : ℂ) (-z) = ∏' l : L.lattice, wFactor (l : ℂ) z := by
    have e := (Equiv.neg L.lattice).tprod_eq (fun l : L.lattice => wFactor (l : ℂ) (-z))
    rw [← e]
    congr 1
    ext l
    simp [wFactor_neg_neg]
  unfold wSigma
  rw [hP]
  ring
end Formalism.L2.Th1.F
