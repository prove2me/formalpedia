-- Prove2me | solution 1 for Formalism.REAL.WDA_op
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:34:10.730618+00:00
-- url     : https://prove2.me/submissions/ecb0f813-f3a5-461e-bd74-5ace436a2dbe

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementA
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_SumOfSquaresIdentityHolds

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
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
  {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V}
namespace Formalism.REAL
theorem _root_.solution (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) :
    (2 • CasK ε E - Cas E) = ∑ a, ∑ b, ((sgn ε a b : ℂ)) • (E a b * E b a) := by
  simp only [CasK, Cas, Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  unfold sgn
  split_ifs with h
  · simp [two_smul]
  · simp
end Formalism.REAL
