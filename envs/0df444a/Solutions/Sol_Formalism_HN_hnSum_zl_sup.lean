-- Prove2me | solution 1 for Formalism.HN.hnSum_zl_sup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:27.113387+00:00
-- url     : https://prove2.me/submissions/4dab7de6-aa99-43fb-b802-2e1d0e36d0bc

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermod
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PolygonSlopeSum
import Theorems.Thm_Formalism_HN_hnSum_mem_zl
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
namespace Formalism.HN
theorem _root_.solution (A B : Submodule R V) : zl ρ (A ⊔ B) = zl ρ A ⊔ zl ρ B := by
  apply le_antisymm
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := (hnSum_mem_zl ρ _ y).1 hy
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add]
    exact Submodule.add_mem_sup ((hnSum_mem_zl ρ A _).2 ⟨a, ha, rfl⟩)
      ((hnSum_mem_zl ρ B _).2 ⟨b, hb, rfl⟩)
  · exact sup_le (hnSum_zl_mono ρ le_sup_left) (hnSum_zl_mono ρ le_sup_right)
end Formalism.HN
