-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.le_degree
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:39:39.422631+00:00
-- url     : https://prove2.me/submissions/94d08d78-2d41-48be-bb6a-6d71831504b5

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeOrd
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeDiv
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeMin
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeVal
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ConjNeSelfOfCM

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
open Formalism Formalism.L2 Formalism.L2.Pj
open MvPowerSeries NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} [StarRing (𝓞 E)]
namespace Formalism.L2.Pj
namespace Crude
theorem _root_.solution {σ : Type} (α : σ →₀ ℕ) (s : σ) : α s ≤ α.degree := by
  by_cases hs : s ∈ α.support
  · have hd : α.degree = ∑ i ∈ α.support, α i := rfl
    rw [hd]
    exact Finset.single_le_sum (fun i _ => Nat.zero_le (α i)) hs
  · have h0 : α s = 0 := by simpa using hs
    rw [h0]
    exact Nat.zero_le _
end Crude
end Formalism.L2.Pj
