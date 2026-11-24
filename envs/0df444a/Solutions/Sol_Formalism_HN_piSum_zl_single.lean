-- Prove2me | solution 1 for Formalism.HN.piSum_zl_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:48:27.815328+00:00
-- url     : https://prove2.me/submissions/2fad4c6a-8344-4906-bcc1-ac9246e5a423

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermod
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PolygonSlopeSum
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_ShortVector
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PiSumForallInsertOnly
import Theorems.Thm_Formalism_HN_piSum_piReal_single
import Theorems.Thm_Formalism_HN_hnSum_mem_zl


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
variable {R : Type*} [Ring R] {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*}
  [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
variable (ρ : ∀ i, V i →+ E i)
namespace Formalism.HN
theorem _root_.solution (i : ι) (N : Submodule R (V i)) :
    zl (piReal ρ) (N.map (LinearMap.single R V i)) =
      (zl (ρ i) N).map ((piSum_emb E i).restrictScalars ℤ) := by
  ext y
  rw [hnSum_mem_zl (piReal ρ) (N.map (LinearMap.single R V i)) y,
    Submodule.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hx
    exact ⟨ρ i v, (hnSum_mem_zl (ρ i) N (ρ i v)).2 ⟨v, hv, rfl⟩,
      (piSum_piReal_single ρ i v).symm⟩
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨v, hv, rfl⟩ := (hnSum_mem_zl (ρ i) N w).1 hw
    exact ⟨LinearMap.single R V i v, Submodule.mem_map_of_mem hv, piSum_piReal_single ρ i v⟩
end Formalism.HN
