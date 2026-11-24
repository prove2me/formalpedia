-- Prove2me | solution 1 for Formalism.L2.Pj.LocalUnitReduction.finRed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:16:42.647327+00:00
-- url     : https://prove2.me/submissions/903b21e5-ceb6-4b08-a26d-3631b150090d

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LocalUnitReduction_FinRedStatement
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LocalUnitReduction_IsUnitMkOfForallPrime
import Theorems.Thm_Formalism_L2_Pj_LocalUnitReduction_mem_sup_ker
import Theorems.Thm_Formalism_L2_Pj_LocalUnitReduction_mem_of_forall_sup_ker

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.LocalUnitReduction
namespace Formalism.L2.Pj.LocalUnitReduction
theorem _root_.solution : FinRedStatement := by
  intro K' Fr _ _ _ J ι _ R _ _ φ hinj hone hloc hfin
  let Ψ : Fr ⧸ J →ₐ[K'] (∀ c, R c ⧸ Ideal.map (φ c) J) :=
    Pi.algHom _ _ fun c => Ideal.quotientMapₐ (Ideal.map (φ c) J) (φ c) Ideal.le_comap_map
  have hinjΨ : Function.Injective Ψ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.Quotient.eq_zero_iff_mem]
    refine mem_of_forall_sup_ker J φ hinj hone fun c => mem_sup_ker J φ (hloc c) ?_
    have hc := congr_fun hx c
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact hc
  haveI : ∀ c, FiniteDimensional K' (R c ⧸ Ideal.map (φ c) J) := fun c => (hfin c).1
  haveI : ∀ c, IsReduced (R c ⧸ Ideal.map (φ c) J) := fun c => (hfin c).2
  exact ⟨FiniteDimensional.of_injective Ψ.toLinearMap hinjΨ, isReduced_of_injective Ψ hinjΨ⟩
end Formalism.L2.Pj.LocalUnitReduction
