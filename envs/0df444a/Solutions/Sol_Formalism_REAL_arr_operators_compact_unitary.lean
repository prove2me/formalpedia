-- Prove2me | solution 1 for Formalism.REAL.arr_operators_compact_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:43:14.062726+00:00
-- url     : https://prove2.me/submissions/7e45b852-0243-4aff-a0fe-2f0051dfc26a

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactGeneratorRaisesPfil
import Theorems.Thm_Formalism_REAL_pointwise_operator_apply
import Theorems.Thm_Formalism_REAL_factorAction_adjoint

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
theorem _root_.solution {j : ℕ} (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V)
    (hU : IsUnitary ε E) : KUnit ε (arrE E j) := by
  intro a b hab F G
  have hs : (sgn ε a b : ℂ) = 1 := by
    unfold sgn
    rw [if_pos hab]
    simp
  have hpt : ⟪ptE E a b F, G⟫_ℂ = ⟪F, ptE E b a G⟫_ℂ := by
    rw [PiLp.inner_apply, PiLp.inner_apply]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    rw [pointwise_operator_apply, pointwise_operator_apply, hU a b (F α) (G α), hs, one_mul]
  show ⟪((∑ i : Fin j, factorAction i a b) + ptE E a b : Module.End ℂ (Arr V n j)) F, G⟫_ℂ =
    ⟪F, ((∑ i : Fin j, factorAction i b a) + ptE E b a : Module.End ℂ (Arr V n j)) G⟫_ℂ
  rw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.sum_apply,
    inner_add_left, inner_add_right, sum_inner, inner_sum, hpt]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => factorAction_adjoint i a b F G)
end Formalism.REAL
