-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.DescP.HiOrd.dmonN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:46:19.772037+00:00
-- url     : https://prove2.me/submissions/c37d2cef-eefd-4db8-80be-aac171d3c56e

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
variable {k : Type} [CommRing k] {n d : ℕ}
namespace Formalism.L2.FormalSeriesBounds.DescP
namespace HiOrd
theorem _root_.solution (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → k)
    (m : ι →₀ ℕ) {K : ℕ} {g : PS k n d} (h : HiOrd (K + m.degree) g) : HiOrd K (DmonN F cp u m g) := by
  unfold DmonN
  refine HiOrd.foldr F cp u m _ K g ?_
  rw [Finset.sum_map_toList, ← Finsupp.degree_eq_sum]
  exact h
end HiOrd
end Formalism.L2.FormalSeriesBounds.DescP
