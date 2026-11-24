-- Prove2me | solution 1 for Formalism.REAL.CasK_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:12:39.25749+00:00
-- url     : https://prove2.me/submissions/02ebdcc6-459e-4f86-a928-eb6c5e8fd1d7

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactArrFiniteDimensional

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
namespace Formalism.REAL
theorem _root_.solution {j : ℕ} {ε : Fin n → Bool} (X : Fin n → Fin n → Module.End ℂ (Arr V n j))
    (G : Arr V n j) (α : Fin j → Fin n × Fin n) :
    CasK ε X G α = ∑ c, ∑ d, if ε c = ε d then X c d (X d c G) α else 0 := by
  simp only [CasK, LinearMap.sum_apply, WithLp.ofLp_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  split_ifs <;> simp
end Formalism.REAL
