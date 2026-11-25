-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.ValuationNonnegativity.valuation_nonneg_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:34:23.429442+00:00
-- url     : https://prove2.me/submissions/2270084c-9dc8-4264-a976-aa2de2ee9fda

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_IndependenceBoundRaw
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_ValuationNonnegativity_valuation_nonneg_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.L2.FormalSeriesBounds.ValuationNonnegativity
variable {C : Type} [Field C] {V : VF C}
namespace Formalism.L2.FormalSeriesBounds.ValuationNonnegativity
theorem _root_.solution {x y : C} (hy : y ≠ 0) (h : V.v y ≤ V.v x) : V.Ge 0 (x / y) := by
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp (fun h' => hy ((V.v.top_iff).mp h'))
  have hx : x = (x / y) * y := by field_simp
  rw [valuation_nonneg_iff]
  by_contra hlt
  push_neg at hlt
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hlt)
  have h2 : V.v x = ((s + r : ℝ) : WithTop ℝ) := by
    rw [hx, V.v.map_mul, ← hs, ← hr, WithTop.coe_add]
  rw [← hs] at hlt
  rw [h2, ← hr] at h
  have h3 : s < 0 := by exact_mod_cast hlt
  have h4 : r ≤ s + r := by exact_mod_cast h
  linarith
end Formalism.L2.FormalSeriesBounds.ValuationNonnegativity
