-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lfockq_cast
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:54:08.76478+00:00
-- url     : https://prove2.me/submissions/4076a7df-64b4-4772-b9f2-e08f79285f20

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockqLemmas
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockRowAdj
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQRowDivAdj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.REAL
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {σ : Type*} (f g : MvPolynomial σ ℚ) :
    ((fockQ f g : ℚ) : ℂ) = fockF (map (Rat.castHom ℂ) f) (map (Rat.castHom ℂ) g) := by
  unfold fockQ fockF
  rw [MvPolynomial.support_map_of_injective _ (Rat.castHom ℂ).injective]
  push_cast
  refine Finset.sum_congr rfl fun m _ => ?_
  simp [MvPolynomial.coeff_map]
end Formalism.GradedWeylDivisibility
