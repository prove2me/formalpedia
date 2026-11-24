-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.tyS_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:33:27.850176+00:00
-- url     : https://prove2.me/submissions/986af9a2-46ac-45f6-b45b-4895a20dee30

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAxes
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ConstMemTypeSetOfNonneg
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_tyS_pow
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_tyS_of_ne

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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
variable {l : ℕ} (hl : 2 ≤ l)
include hl
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (a : ℕ → C) (f : PowerSeries C) (h1 : ∀ s, PowerSeries.coeff (l ^ s) f = a s)
    (h2 : ∀ m, (∀ s, l ^ s ≠ m) → PowerSeries.coeff m f = 0) : tyS l a = f := by
  ext m
  by_cases h : ∃ s, l ^ s = m
  · obtain ⟨s, rfl⟩ := h
    rw [coeff_tyS_pow hl, h1]
  · push_neg at h
    rw [coeff_tyS_of_ne a m h, h2 m h]
end Formalism.L2.FormalSeriesBounds
