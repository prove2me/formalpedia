-- Prove2me | solution 1 for Formalism.HN.piSum_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:32:14.976335+00:00
-- url     : https://prove2.me/submissions/f7435c2c-b87d-4efa-bbb8-a17bc0fd2bd3

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermod
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PolygonSlopeSum
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_ShortVector
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PiSumForallInsertOnly
import Theorems.Thm_Formalism_HN_piSum_emb_injective
import Theorems.Thm_Formalism_HN_piSum_piReal_single
import Theorems.Thm_Formalism_HN_piSum_zl_single
import Theorems.Thm_Formalism_HN_piSum_transfer

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
variable [∀ i, FiniteDimensional ℝ (E i)]
namespace Formalism.HN
theorem _root_.solution (i : ι) (N : Submodule R (V i)) (hN : IsLat (ρ i) N) :
    IsLat (piReal ρ) (N.map (LinearMap.single R V i)) ∧
    rk (piReal ρ) (N.map (LinearMap.single R V i)) = rk (ρ i) N ∧
    deg (piReal ρ) (N.map (LinearMap.single R V i)) = deg (ρ i) N := by
  have himg := piSum_zl_single ρ i N
  have := hN.2
  obtain ⟨hd, hr, hc⟩ := piSum_transfer i (zl (ρ i) N)
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.1 hx
    obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.1 hy
    rw [piSum_piReal_single, piSum_piReal_single] at hxy
    rw [hN.1 ha hb (piSum_emb_injective i hxy)]
  · rw [himg]
    exact hd
  · unfold rk
    rw [himg]
    exact hr
  · unfold deg
    rw [himg]
    unfold Formalism.F.deg
    rw [hc]
end Formalism.HN
