-- Prove2me | solution 1 for Formalism.REAL.symmetrization_equivariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:00:19.199039+00:00
-- url     : https://prove2.me/submissions/f0c3372e-70f7-4931-912e-80a1ccc9e9f0

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactGeneratorRaisesPfil
import Theorems.Thm_P2M_Formalism_REAL_factorAction_apply__702f0fa4e7c4
import Theorems.Thm_Formalism_REAL_arr_operator_apply
import Theorems.Thm_Formalism_REAL_sum_update_first_index_swap
import Theorems.Thm_Formalism_REAL_sum_update_second_index_swap
import Theorems.Thm_Formalism_REAL_commutator_word_operator_sum
import Theorems.Thm_Formalism_REAL_theta_map_apply

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
theorem _root_.solution (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) {j : ℕ} (c d : Fin n)
    (F : Arr V n j) : thetaA E j (arrE E j c d F) = E c d (thetaA E j F) := by
  have hder : ∀ α : Fin j → Fin n × Fin n, E c d (u1W E α (F α)) = u1W E α (E c d (F α)) +
      ∑ i, ((if (α i).1 = d then u1W E (Function.update α i (c, (α i).2)) (F α) else 0) -
        (if (α i).2 = c then u1W E (Function.update α i ((α i).1, d)) (F α) else 0)) := by
    intro α
    have h := LinearMap.congr_fun (commutator_word_operator_sum E hE c d j α) (F α)
    rw [LinearMap.sub_apply, LinearMap.sum_apply] at h
    have h' : E c d (u1W E α (F α)) - u1W E α (E c d (F α)) =
        ∑ i, ((if d = (α i).1 then u1W E (Function.update α i (c, (α i).2)) else 0) -
          (if (α i).2 = c then u1W E (Function.update α i ((α i).1, d)) else 0)) (F α) := h
    rw [← sub_eq_iff_eq_add', h']
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [eq_comm (a := d)]
    split_ifs <;> simp
  have hkey : ∑ α : Fin j → Fin n × Fin n, ∑ i, u1W E α (factorAction i c d F α) =
      ∑ α : Fin j → Fin n × Fin n, ∑ i,
        ((if (α i).1 = d then u1W E (Function.update α i (c, (α i).2)) (F α) else 0) -
          (if (α i).2 = c then u1W E (Function.update α i ((α i).1, d)) (F α) else 0)) := by
    conv_lhs => rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have e1 : ∀ α : Fin j → Fin n × Fin n, u1W E α (factorAction i c d F α) =
        (if (α i).1 = c then u1W E α (F (Function.update α i (d, (α i).2))) else 0) -
        (if (α i).2 = d then u1W E α (F (Function.update α i ((α i).1, c))) else 0) := by
      intro α; rw [factorAction_apply']; split_ifs <;> simp
    simp only [e1, Finset.sum_sub_distrib]
    rw [sum_update_first_index_swap i c d (fun α β => u1W E α (F β)), sum_update_second_index_swap i c d (fun α β => u1W E α (F β))]
  rw [theta_map_apply, theta_map_apply, map_sum]
  simp only [arr_operator_apply, map_add, map_sum, hder, Finset.sum_add_distrib]
  rw [hkey]
  exact add_comm _ _
end Formalism.REAL
