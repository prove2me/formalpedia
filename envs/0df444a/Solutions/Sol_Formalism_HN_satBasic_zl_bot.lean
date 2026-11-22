-- Prove2me | solution 1 for Formalism.HN.satBasic_zl_bot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:27:39.319607+00:00
-- url     : https://prove2.me/submissions/70ead47c-3a0c-4a89-8181-b7034fc02bb9

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_MuMaxAttained
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Theorems.Thm_Formalism_HN_satR_mem_zl


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
namespace Formalism.HN
theorem _root_.solution : zl ρ (⊥ : Submodule R V) = ⊥ := by
  ext x
  rw [satR_mem_zl, Submodule.mem_bot]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Submodule.mem_bot] at hy
    rw [hy, map_zero]
  · intro hx
    exact ⟨0, Submodule.zero_mem _, by rw [hx, map_zero]⟩
end Formalism.HN
