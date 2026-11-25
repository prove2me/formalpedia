-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.DescP.hiOrd_sub_trunc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:35:10.981943+00:00
-- url     : https://prove2.me/submissions/1d7d0b3f-9d51-4d7d-8155-333247ea3198

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
theorem _root_.solution (f : PS k n d) (D : ℕ) :
    HiOrd (D + 1) (f - ((trunc' k (cst D) f : MvPolynomial _ k) : PS k n d)) := by
  intro μ hμ
  rw [map_sub, MvPolynomial.coeff_coe, MvPowerSeries.coeff_trunc', if_pos, sub_self]
  intro i
  have h1 : μ i ≤ Finsupp.degree μ := Finsupp.le_degree i μ
  simp [cst]
  omega
end Formalism.L2.FormalSeriesBounds.DescP
