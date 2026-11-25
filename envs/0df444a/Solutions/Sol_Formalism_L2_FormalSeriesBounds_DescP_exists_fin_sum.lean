-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.DescP.exists_fin_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:34:20.952009+00:00
-- url     : https://prove2.me/submissions/0940ecd4-94b9-4f21-a77a-04e2420a925f

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieDesc
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePDescJet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.DescP
open MvPowerSeries Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
namespace Formalism.L2.FormalSeriesBounds.DescP
theorem _root_.solution {α M : Type} [AddCommMonoid M] (s : Finset α) (g : α → M) :
    ∃ (N : ℕ) (e : Fin N → α), (∀ j, e j ∈ s) ∧ ∑ x ∈ s, g x = ∑ j, g (e j) := ⟨s.card, fun j => (s.equivFin.symm j : α), fun j => (s.equivFin.symm j).2, by
    rw [← Finset.sum_coe_sort s, ← Equiv.sum_comp s.equivFin.symm]⟩
end Formalism.L2.FormalSeriesBounds.DescP
