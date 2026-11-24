-- Prove2me | solution 1 for Formalism.REAL.factorAction_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:34:55.970796+00:00
-- url     : https://prove2.me/submissions/25813167-35ed-498a-a3b8-699683178818

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactGeneratorRaisesPfil
import Theorems.Thm_P2M_Formalism_REAL_factorAction_apply__702f0fa4e7c4
import Theorems.Thm_Formalism_REAL_sum_update_first_index_swap
import Theorems.Thm_Formalism_REAL_sum_update_second_index_swap

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
theorem _root_.solution {j : ℕ} (i : Fin j) (a b : Fin n) (F G : Arr V n j) :
    ⟪factorAction i a b F, G⟫_ℂ = ⟪F, factorAction i b a G⟫_ℂ := by
  have hL : ∀ α, ⟪factorAction i a b F α, G α⟫_ℂ =
      (if (α i).1 = a then ⟪F (Function.update α i (b, (α i).2)), G α⟫_ℂ else 0) -
      (if (α i).2 = b then ⟪F (Function.update α i ((α i).1, a)), G α⟫_ℂ else 0) := by
    intro α; rw [factorAction_apply']; split_ifs <;> simp [inner_sub_left]
  have hR : ∀ β, ⟪F β, factorAction i b a G β⟫_ℂ =
      (if (β i).1 = b then ⟪F β, G (Function.update β i (a, (β i).2))⟫_ℂ else 0) -
      (if (β i).2 = a then ⟪F β, G (Function.update β i ((β i).1, b))⟫_ℂ else 0) := by
    intro β; rw [factorAction_apply']; split_ifs <;> simp [inner_sub_right]
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp only [hL, hR, Finset.sum_sub_distrib]
  rw [sum_update_first_index_swap i a b (fun α β => ⟪F β, G α⟫_ℂ), sum_update_second_index_swap i a b (fun α β => ⟪F β, G α⟫_ℂ)]
end Formalism.REAL
