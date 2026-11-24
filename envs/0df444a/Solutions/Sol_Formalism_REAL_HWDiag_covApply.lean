-- Prove2me | solution 1 for Formalism.REAL.HWDiag_covApply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:28:02.867599+00:00
-- url     : https://prove2.me/submissions/d4689716-cc3b-43a9-8d24-99f728da5d60

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementB
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_HWDiag
import Theorems.Thm_Formalism_REAL_HWDiag_cov

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
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) (k : ℕ) (a b c d : Fin n) (v : V) :
    epow E k a b (E c d v) = E c d (epow E k a b v) -
      ((if d = a then epow E k c b v else 0) - (if b = c then epow E k a d v else 0)) := by
  have h := congrArg (fun f : Module.End ℂ V => f v) (HWDiag_cov E hE k a b c d)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  have h' : epow E k a b (E c d v) = E c d (epow E k a b v) -
      (E c d (epow E k a b v) - epow E k a b (E c d v)) := by abel
  rw [h', h]
  split_ifs <;> simp
end Formalism.REAL
