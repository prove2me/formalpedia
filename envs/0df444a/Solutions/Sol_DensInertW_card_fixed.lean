-- Prove2me | solution 1 for DensInertW.card_fixed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:56:55.009668+00:00
-- url     : https://prove2.me/submissions/c107df6c-3d7c-4eb9-a08a-4b3da4121206

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_ExistsTraceNeZero
import Theorems.Thm_DensInertW_one_lt_q
import Theorems.Thm_DensInertW_frob_algebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
open DensInertW
variable {K L : Type} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]
namespace DensInertW
theorem _root_.solution [DecidableEq L] : #{x : L | x ^ Fintype.card K = x} = Fintype.card K := by
  have hq := one_lt_q (K := K)
  apply le_antisymm
  · have hne := FiniteField.X_pow_card_sub_X_ne_zero L hq
    calc #{x : L | x ^ Fintype.card K = x}
        ≤ ((X ^ Fintype.card K - X : L[X]).roots.toFinset).card := by
          apply card_le_card
          intro x hx
          simp only [mem_filter, mem_univ, true_and] at hx
          rw [Multiset.mem_toFinset, mem_roots hne]
          simp [hx]
      _ ≤ Multiset.card (X ^ Fintype.card K - X : L[X]).roots := Multiset.toFinset_card_le _
      _ ≤ (X ^ Fintype.card K - X : L[X]).natDegree := card_roots' _
      _ = Fintype.card K := FiniteField.X_pow_card_sub_X_natDegree_eq L hq
  · calc Fintype.card K = (univ.image (algebraMap K L)).card := by
          rw [card_image_of_injective _ (algebraMap K L).injective, card_univ]
      _ ≤ _ := by
          apply card_le_card
          intro x hx
          obtain ⟨a, -, rfl⟩ := mem_image.mp hx
          simp [frob_algebraMap]
end DensInertW
