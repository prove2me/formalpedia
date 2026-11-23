-- Prove2me | solution 1 for Formalism.HN.hnSum_isLat_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:01:02.271799+00:00
-- url     : https://prove2.me/submissions/854e88dd-c001-4818-b603-5389dff7e113

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermod
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PolygonSlopeSum
import Theorems.Thm_Formalism_HN_hnSum_zl_mono

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
theorem _root_.solution {L N : Submodule R V} (hL : IsLat ρ L) (h : N ≤ L) : IsLat ρ N := by
  refine ⟨hL.1.mono h, ?_⟩
  haveI := hL.2
  exact DiscreteTopology.of_continuous_injective
    (f := fun y : zl ρ N => (⟨y.1, hnSum_zl_mono ρ h y.2⟩ : zl ρ L))
    (continuous_subtype_val.subtype_mk _)
    (by
      intro a b hab
      simp only [Subtype.mk.injEq] at hab
      exact Subtype.ext hab)
end Formalism.HN
