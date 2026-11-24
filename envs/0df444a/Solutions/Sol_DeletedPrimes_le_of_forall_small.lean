-- Prove2me | solution 1 for DeletedPrimes.le_of_forall_small
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:12:40.958794+00:00
-- url     : https://prove2.me/submissions/4705977b-c016-422f-b978-20d108a295e2

import Definitions.Def_DeletedPrimes_Legendre
import Definitions.Def_DeletedPrimes_Exponents
import Definitions.Def_DeletedPrimes_GoodScales
import Definitions.Def_DeletedPrimes_CompositeFloor

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution {κ α B η₀ : ℝ} (hκ : 0 < κ) (hη₀ : 0 < η₀)
    (h : ∀ η : ℝ, 0 < η → η < η₀ → κ * (α - η) ≤ B) : κ * α ≤ B := by
  by_contra hlt
  push Not at hlt
  set η := min (η₀ / 2) ((κ * α - B) / (2 * κ)) with hηdef
  have hη0 : 0 < η := lt_min (by linarith) (div_pos (by linarith) (by linarith))
  have hη1 : η < η₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hη2 : κ * η ≤ (κ * α - B) / 2 := by
    have : η ≤ (κ * α - B) / (2 * κ) := min_le_right _ _
    calc κ * η ≤ κ * ((κ * α - B) / (2 * κ)) := mul_le_mul_of_nonneg_left this hκ.le
      _ = (κ * α - B) / 2 := by field_simp
  have := h η hη0 hη1
  nlinarith
end DeletedPrimes
