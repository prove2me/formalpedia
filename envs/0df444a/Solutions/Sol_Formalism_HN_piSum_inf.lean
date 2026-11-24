-- Prove2me | solution 1 for Formalism.HN.piSum_inf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:48:27.035814+00:00
-- url     : https://prove2.me/submissions/f4768bd2-b31d-4a58-be55-0887ffdbee90

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermod
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PolygonSlopeSum
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_ShortVector
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PiSumForallInsertOnly
import Theorems.Thm_Formalism_HN_piSum_T_vanish

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
theorem _root_.solution (L : ∀ i, Submodule R (V i)) (a : ι) (s : Finset ι) (ha : a ∉ s) :
    piSumS L a ⊓ piSumT L s = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.1 hx
  obtain ⟨v, -, rfl⟩ := Submodule.mem_map.1 hx1
  have h := piSum_T_vanish L s hx2 a ha
  have hv : v = 0 := by
    simpa using h
  rw [Submodule.mem_bot, hv, map_zero]
end Formalism.HN
