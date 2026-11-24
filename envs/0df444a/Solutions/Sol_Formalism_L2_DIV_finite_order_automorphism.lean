-- Prove2me | solution 1 for Formalism.L2.DIV.finite_order_automorphism
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:42:47.53956+00:00
-- url     : https://prove2.me/submissions/32673243-a25d-4c31-8b89-b6347a452481

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_DivisibilityProofs_TuplesP
import Theorems.Thm_Formalism_L2_DIV_c_class
import Theorems.Thm_Formalism_L2_DIV_c_unit_pow
import Theorems.Thm_Formalism_L2_DIV_mem_kills


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain TensorProduct Formalism.UG Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.UG.P
open scoped nonZeroDivisors
open Formalism Formalism.L2 Formalism.L2.DIV
namespace Formalism.L2.DIV
theorem _root_.solution : FinOrdAuto := by
  intro F E _ _ _ _ _ L _ ξ hξ
  obtain ⟨h1, N, hN, h2⟩ := Subgroup.mem_inf.mp hξ
  rw [mem_kills] at h1
  obtain ⟨m, hm, hu⟩ := c_unit_pow (F := F) (E := E) N hN
  rw [CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
  refine ⟨Fintype.card (ClassGroup (𝓞 E)) * m, Nat.mul_pos Fintype.card_pos hm, ?_⟩
  ext x
  obtain ⟨e, he⟩ := c_class x
  have h3 : ξ (ratId F E e) = 1 := h1 ⟨e, rfl⟩
  have h4 : ξ ((x ^ Fintype.card (ClassGroup (𝓞 E)) * (ratId F E e)⁻¹) ^ m) = 1 := h2 (hu _ he)
  rw [map_pow, map_mul, map_inv, h3, inv_one, mul_one, map_pow, ← pow_mul] at h4
  rw [MonoidHom.pow_apply, h4, MonoidHom.one_apply]
end Formalism.L2.DIV
