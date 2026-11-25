-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.coeff_tyS_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:36:09.978858+00:00
-- url     : https://prove2.me/submissions/835638c8-a51f-4ded-adb5-196efa68e26e

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeOfPowEqOne
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffAlongCvCongr

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
theorem _root_.solution {l : ℕ} (hl : 2 ≤ l) (a b : ℕ → C) (N : ℕ) (hab : ∀ i < N, a i = b i) (m : ℕ)
    (hm : m < l ^ N) : PowerSeries.coeff m (tyS l a) = PowerSeries.coeff m (tyS l b) := by
  simp only [tyS, PowerSeries.coeff_mk]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hs : l ^ s = m
  · rw [if_pos hs, if_pos hs]
    apply hab
    by_contra hc
    push_neg at hc
    have h1 : l ^ N ≤ l ^ s := Nat.pow_le_pow_right (by omega) hc
    rw [hs] at h1
    exact absurd hm (not_lt.2 h1)
  · rw [if_neg hs, if_neg hs]
end Formalism.L2.FormalSeriesBounds
