-- Prove2me | solution 1 for Formalism.IndefR.LocBrg.newton_step
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:54:23.462579+00:00
-- url     : https://prove2.me/submissions/af964609-5335-42c4-b554-66561af26267

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LocalNormSurjectivity_FinNormSurj
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LocalNormSurjectivity_WittHS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.LocBrg
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
local notation "vv" => (Valued.v : Valuation L (WithZero (Multiplicative ℤ)))
variable (u : L)
namespace Formalism.IndefR.LocBrg
theorem _root_.solution (k : ℕ) (hs : vv (newtonSq u k - 1) < 1) (h2 : vv (2 : L) = 1) :
    vv (newtonSq u k) = 1 ∧
      newtonSq u (k + 1) * newtonSq u (k + 1) - u =
        (newtonSq u k * newtonSq u k - u) ^ 2 / (4 * newtonSq u k ^ 2) ∧
      vv (newtonSq u (k + 1) - newtonSq u k) = vv (newtonSq u k * newtonSq u k - u) := by
  set x := newtonSq u k with hx
  have hx1 : vv x = 1 := by
    have hxe : x = (x - 1) + 1 := by ring
    have hlt : vv (x - 1) < vv (1 : L) := by rwa [Valuation.map_one]
    rw [hxe, Valuation.map_add_eq_of_lt_right (v := vv) hlt, Valuation.map_one]
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, Valuation.map_zero] at hx1
    exact zero_ne_one hx1
  have h20 : (2 : L) ≠ 0 := by
    intro h
    rw [h, Valuation.map_zero] at h2
    exact zero_ne_one h2
  have hnext : newtonSq u (k + 1) = x - (x * x - u) / (2 * x) := rfl
  have h40 : (4 : L) ≠ 0 := by
    rw [show (4 : L) = 2 * 2 by norm_num]
    exact mul_ne_zero h20 h20
  refine ⟨hx1, ?_, ?_⟩
  · rw [hnext]
    field_simp
    ring
  · rw [hnext, show x - (x * x - u) / (2 * x) - x = -((x * x - u) / (2 * x)) by ring, Valuation.map_neg,
      Valuation.map_div, Valuation.map_mul, h2, hx1, one_mul, div_one]
end Formalism.IndefR.LocBrg
