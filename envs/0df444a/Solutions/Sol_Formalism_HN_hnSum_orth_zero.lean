-- Prove2me | solution 1 for Formalism.HN.hnSum_orth_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:26.742612+00:00
-- url     : https://prove2.me/submissions/181f246c-426e-4e69-be14-f6546278ce8c

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermod
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PolygonSlopeSum

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
variable {R V E : Type*} [Ring R] [AddCommGroup V] [Module R V] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (ρ : V →+ E)
variable [FiniteDimensional ℝ E]
namespace Formalism.HN
theorem _root_.solution {A : Submodule R V} (hA : IsLat ρ A) {x : V} (hx : x ∈ A)
    (h : inner ℝ (ρ x) (ρ x) = 0) : x = 0 := by
  have h0 : ρ x = 0 := inner_self_eq_zero.1 h
  exact hA.1 hx A.zero_mem (by rw [h0, map_zero])
end Formalism.HN
