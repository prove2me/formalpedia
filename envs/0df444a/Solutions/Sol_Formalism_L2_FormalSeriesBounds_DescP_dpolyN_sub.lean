-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.DescP.dpolyN_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:40:51.374978+00:00
-- url     : https://prove2.me/submissions/2dd7b903-0cf8-4159-a826-e41992658ef5

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
theorem _root_.solution (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → k)
    (P : MvPolynomial ι k) (g : PS k n d) (S : Finset (ι →₀ ℕ)) (hS : P.support ⊆ S) :
    DpolyN F cp u P g = ∑ m ∈ S, MvPowerSeries.C (P.coeff m) * DmonN F cp u m g := by
  unfold DpolyN
  refine Finset.sum_subset hS fun m _ hm => ?_
  rw [MvPolynomial.notMem_support_iff.1 hm, map_zero, zero_mul]
end Formalism.L2.FormalSeriesBounds.DescP
