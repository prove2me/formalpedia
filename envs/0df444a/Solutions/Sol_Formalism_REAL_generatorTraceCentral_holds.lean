-- Prove2me | solution 1 for Formalism.REAL.generatorTraceCentral_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:34:59.946415+00:00
-- url     : https://prove2.me/submissions/297e1e7f-2c81-47a8-88a1-de967eef71eb

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementB
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorPowUpperVanishHolds
import Theorems.Thm_Formalism_REAL_generatorPowCovariance_holds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution : EtrCentral := by
  intro A _ n E hE k c d
  have hc := generatorPowCovariance_holds A n E hE k
  unfold etr
  rw [Finset.sum_mul, Finset.mul_sum, ← sub_eq_zero, ← Finset.sum_sub_distrib]
  have h1 : ∀ a, epow E k a a * E c d - E c d * epow E k a a =
      -((if d = a then epow E k c a else 0) - (if a = c then epow E k a d else 0)) := by
    intro a
    rw [← hc a a c d]
    abel
  simp only [h1, Finset.sum_neg_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, sub_self, neg_zero]
end Formalism.REAL
