-- Prove2me | solution 1 for Formalism.HN.satBasic_zl_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:27:39.411896+00:00
-- url     : https://prove2.me/submissions/d815fa62-6e78-45ea-8123-5e1c006e882c

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
theorem _root_.solution {A B : Submodule R V} (h : A ≤ B) : zl ρ A ≤ zl ρ B := by
  intro x hx
  rw [satR_mem_zl] at hx ⊢
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨y, h hy, rfl⟩
end Formalism.HN
