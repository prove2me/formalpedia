-- Prove2me | solution 1 for Bl.general_b_fact_right_further.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:26:09.274112+00:00
-- url     : https://prove2.me/submissions/a8251e92-0b2f-472f-b82a-c446e60fb4ad

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactRightFurther_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_right_further
namespace Bl.general_b_fact_right_further
theorem _root_.solution :
  ∀ {n : Nat} (J : Finset.{0} (Fin n)) {k : Nat} (h : Eq.{1} (Finset.card.{0} J) k) (i : Fin k),
  Eq.{1}
    (Finset.card.{0}
      (Finset.filter.{0} (fun (x : Fin n) ↦ LT.lt.{0} x (DFunLike.coe.{1, 1, 1} (Finset.orderEmbOfFin.{0} J h) i)) J))
    i.val := by
  intro n J k h i
  have key : Finset.filter (fun (x : Fin n) ↦ x < J.orderEmbOfFin h i) J
      = (Finset.Iio i).map (J.orderEmbOfFin h).toEmbedding := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_Iio]
    constructor
    · rintro ⟨hx, hlt⟩
      have hr : x ∈ Set.range (J.orderEmbOfFin h) := by
        rw [Finset.range_orderEmbOfFin]; exact hx
      obtain ⟨j, rfl⟩ := hr
      exact ⟨j, (J.orderEmbOfFin h).lt_iff_lt.mp hlt, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨Finset.orderEmbOfFin_mem J h j, (J.orderEmbOfFin h).lt_iff_lt.mpr hj⟩
  rw [key, Finset.card_map, Fin.card_Iio]
end Bl.general_b_fact_right_further
