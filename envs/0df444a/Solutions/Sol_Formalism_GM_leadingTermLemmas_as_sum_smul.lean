-- Prove2me | solution 1 for Formalism.GM.leadingTermLemmas.as_sum_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:33:04.760334+00:00
-- url     : https://prove2.me/submissions/a597c521-6158-4a0a-be46-38c321e346f5

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.leadingTermLemmas
open MvPolynomial Finset Formalism.GM
variable {K : Type} [Field K]
namespace Formalism.GM.leadingTermLemmas
theorem _root_.solution {σ : Type} (f : MvPolynomial σ K) :
    f = ∑ m ∈ f.support, f.coeff m • monomial m (1 : K) := by
  conv_lhs => rw [f.as_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [smul_monomial, smul_eq_mul, mul_one]
end Formalism.GM.leadingTermLemmas
