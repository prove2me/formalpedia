-- Prove2me | solution 1 for Formalism.HN.piSum_T_vanish
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:58:08.940652+00:00
-- url     : https://prove2.me/submissions/ade5ee53-863d-47ab-aca3-5784ec87a961

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermod
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PolygonSlopeSum
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_ShortVector
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PiSumForallInsertOnly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.HN
variable {R : Type*} [Ring R] {ι : Type*} [DecidableEq ι] {V : ι → Type*}
  [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
namespace Formalism.HN
theorem _root_.solution (L : ∀ i, Submodule R (V i)) (s : Finset ι) {x : ∀ i, V i}
    (hx : x ∈ piSumT L s) (j : ι) (hj : j ∉ s) : x j = 0 := by
  have hle : piSumT L s ≤ LinearMap.ker (LinearMap.proj j : (∀ i, V i) →ₗ[R] V j) := by
    refine iSup₂_le fun i hi => ?_
    intro y hy
    obtain ⟨v, -, rfl⟩ := Submodule.mem_map.1 hy
    have hij : j ≠ i := fun h => hj (h ▸ hi)
    rw [LinearMap.mem_ker]
    simp [hij]
  exact LinearMap.mem_ker.1 (hle hx)
end Formalism.HN
