-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.coeff_tyS_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:32:28.217387+00:00
-- url     : https://prove2.me/submissions/894ef51d-1676-4a62-9ebe-d8b72bc3d1e0

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ConstMemTypeSetOfNonneg
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValNonnegLeadingCoeffOfMemTySet

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
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution {l : ℕ} (hl : 2 ≤ l) (a : ℕ → C) (s : ℕ) (ha : ∀ i < s, a i = 0) (m : ℕ) (hm : m < l ^ s) :
    PowerSeries.coeff m (tyS l a) = 0 := by
  simp only [tyS, PowerSeries.coeff_mk]
  apply Finset.sum_eq_zero
  intro t _
  split_ifs with ht
  · apply ha
    by_contra hc
    push_neg at hc
    have : l ^ s ≤ l ^ t := Nat.pow_le_pow_right (by omega) hc
    omega
  · rfl
end Formalism.L2.FormalSeriesBounds
